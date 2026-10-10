[← Back](README.md) | [English](SHIFT7.md) | [Japanese](SHIFT7-ja.md)

# $`R_2^+`$, the thirtieth and thirty-first rounds: the relative far pin at every depth, not-LOW, $`\nu_C = \nu_S = L(\omega+1)`$, and the ω-top up to $`\varepsilon_{\Omega_\omega+1}`$

This page continues [SHIFT6.md](SHIFT6.md) (§3 there is the twenty-ninth round); §1 is the thirtieth round, §2 the thirty-first. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

## 1. The thirtieth round

Three papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-ninth round asked for the change and a referee of this round checked it, or that the papers of §1.1 and §1.2 prove the result independently and both referees found it
proved. None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this). Papers cited: [W07b] (L.2.1) in §1.1 and §1.2,
checked by both referees against the paper; no paper is used in a proved step of §1.3, which does not use FRAG. No Lean file was added: each paper checked its ordinal inputs with a
Lean file that only compares terms (`#eval`, no theorem; green, and identical in the referee's rerun); these count as checks. Levels are numbered as in [SHIFT6.md](SHIFT6.md) (one
higher than in the papers): level 1 is below $`m^* = \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, level 2 is $`[m^*, \psi_{\Omega_1}(\Omega_\omega\cdot 3))`$.

Names. As in [SHIFT3.md](SHIFT3.md) §2.4, $`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$ and $`L(\xi) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot\xi)`$, so (since $`P'`$ is an $`\varepsilon`$-number)

```math
L(1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'),\qquad L(\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1}),\qquad L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P').
```

$`L(\omega)`$ and $`L(\omega+1)`$ are the conjectured names of the left end $`a_0`$ of the first nested pair and of $`\nu`$ (Conjecture NU-NAME, [BREAK.md](BREAK.md) §2, §8). The **lower map** of a pin: a
copy $`h`$ at an outer restart $`\lambda`$ maps a long restart $`\nu`$ inside the offset of $`\lambda`$ to a restart $`\nu''`$; the map $`g`$ that the pin uses below $`\rho_\nu`$ is the lower map, and only
$`h \ge g`$ is known on the moved hereditary parameters. The **pin tree** of a long restart: its prefix restarts inside its landing offset, then theirs, and so on.

### 1.1 The relative far pin at every depth: not-LOW and $`\nu_C \ge L(\omega+1)`$, given FRAG

- **The minor points of the review of [SHIFT6.md](SHIFT6.md) §3.2 are applied** (**2 reviews**). CAP-1 is about the codes below $`P'`$ at level 2 (not the codes in $`[P', P'_1)`$), and with it the
  refereed reduction NU-LOW″ gives more than $`L(1)`$ (see below), which answers the referee's question; $`\Theta`$ of a level shift is read as the shifted reading; the coefficient and the case "the own
  source wins" are written; the order tests are said to test the order only; the open points of the transfer are listed for the referee.
- **BC$`^{\mathrm{rel}}`$, CODE-MON, the pin tree, DOM$`^{\mathrm{rel}}`$, THETA-EQ$`^{\mathrm{rel}}`$, EQUIV$`^{\mathrm{rel}}`$, EQ-F$`^{\mathrm{rel}}`$** (proved; the first and the last three by transfer). For every lower map $`g`$, the transport
  $`T''_g`$ from $`\nu`$ to $`\nu''`$ is a base change of the known kind. A code does not grow under $`g`$ ($`c^g \le c`$), so an induction on the code reaches the codes of the images. The pin tree is
  finite, and every code in it is below the code $`m_\lambda`$ of the root. If the bottom $`\kappa_0`$ of the copy is chosen above $`H(\beta_\lambda)`$ for a suitable $`\beta_\lambda \lt \eta_\lambda`$, every image
  code lies in the domain of the native reading and every image offset lies in $`D`$. EQ-F$`^{\mathrm{rel}}`$ answers the minor point of [SHIFT6.md](SHIFT6.md) §3.1 (EQ-cl for base changes) for the maps $`T''_g`$.
- **FAR-PIN$`^{L,\mathrm{rel}}`$, SIM$`^{\mathrm{rel}}`$** (proved by transfer, given FRAG). For every code $`m \lt P'`$, by one induction on $`m`$, at every restart of level 1:
  (EX$`_m`$) every long restart of code $`m`$ has its exact reach, with the crossing, the lower bound, both sides of EXACT and the pin; (MR$`_{\lt m}`$) the relative multiple pin holds along every
  offset whose long prefix codes are below $`m`$; (RP$`_m`$) the relative pin holds at every relative base of code $`m`$: the nested landing pins, the atom, the code of the image, and the bound of the
  atom. At a nested level the lower map is the transport $`T''`$ of the level above, and $`h \ge g`$ on the hereditary parameters comes from Claim B at the earlier bases (SIM$`^{\mathrm{rel}}`$). Every nested
  code is smaller, so every depth is covered. **This repairs the blocking point b1 of [SHIFT6.md](SHIFT6.md) §3.2** (the referee: b1 is repaired; the induction calls (RP) and (EX) only at smaller
  codes; the cases of the image code are complete). The witnesses $`G(\Omega_5)`$ (depth 2), $`G(\theta_4\cdot\omega^2)`$ and a code with constants read by $`\Theta`$ are worked through.
- **LAND$`^\omega`$, MONO-L$`^\omega`$, FAR-PIN$`^{L,\omega}`$, LONG-CLASS$`^\omega`$, EX$`^w`$ below $`P'`$** (proved, given FRAG). For every long code $`G_2\cdot D + m_0 \lt P'`$:

```math
r(\lambda) = \mathrm{cl}_{\nu^*}(\tau^* + m_0),
```

  where $`\tau^*`$ is the landing code of [SHIFT6.md](SHIFT6.md) §3 (now unwound through long own sources). The reach increases strictly with the code and commutes with the transports, and every code
  below $`P'`$ is an exact atom whose landing offset can be pinned. So no code below $`P'`$ is without EX$`^w`$. For the codes below $`G(\hat\zeta_{23})`$ the exact reach is also proved by the paper of §1.2
  (**2 reviews** at levels 1 and 2).
- **CAP-0 below $`P'`$** (proved, given FRAG). No restart below $`m^*`$ is self-crossing: $`r(\lambda) \lt H(\eta_\lambda + \zeta')`$ with $`\zeta' = \Lambda(m_\lambda) + \omega^2 \lt \omega^{m_\lambda}`$ and $`\eta_\lambda + \zeta' \in D`$.
- **Not-LOW** (proved, given FRAG). With the refereed reduction EX-RED$`^w`$ ([SHIFT6.md](SHIFT6.md) §2.1):

```math
\nu_C \gt m^* = \psi_{\Omega_1}(\Omega_\omega\cdot 2).
```

  **So LOW is false, given FRAG** (1 review). Also no $`\alpha \lt m^*`$ has $`\alpha \le_1 m^*`$, and every $`\le_1`$-predecessor of $`x`$ is at least $`m^*`$.
- **Level 2, CAP-1** (proved by transfer, given FRAG). The same induction for the restarts of level 2 with code below $`P'`$ (there DOM$`^{\mathrm{rel}}`$ holds for free, since $`\pi_\eta \ge P'`$). So no
  restart of level 2 with code below $`P'`$ is self-crossing, in the form that NU-LOW″ ([SHIFT3.md](SHIFT3.md) §2.4) uses.
- **NU-LOW″, NU-LOW″⁺** (proved, given FRAG). From CAP-0 and CAP-1: a final segment of the $`\le_1`$-predecessors of $`x`$ consists of points of level 2, $`x \ge L(\omega)`$, and
  $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + \omega^{\mathbb{G}^\vartheta+1})`$. With LONG-CLASS$`^\omega`$ at level 2 in place of the old class lemma, the exponent of $`\nu_C`$ is at least $`P'`$, and

```math
\nu_C \ge L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P'),\qquad \nu_S \ge L(\omega+1).
```

  This is the lower half of the conjectured name of $`\nu`$. **Wilken's claim holds in $`R_2^C`$ on $`[0, L(\omega+1)]`$, both halves, given FRAG** (the core half by $`[0, L(\omega+1)] \subseteq [0, \nu_C]`$, the names
  half because $`L(\omega+1)`$ is a normal form, Lemma L). The referee checked the arithmetic $`P\cdot\omega^{P'+1} = \omega^{P'+1}`$ and $`P\cdot P' = P'`$. The range moves from $`X_{23}`$ to $`L(\omega+1)`$, far past
  $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (the chain $`L(1) \lt L(\omega) \lt L(\omega+1) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ is checked, §1.5).
- **Not proved** (open, as the paper says): the upper half $`\nu_C \le L(\omega+1)`$; the reach of $`m^*`$; the codes $`\ge P'`$ at level 2 and above; (P), (Q′); $`R_2^S`$ beyond $`\nu_C`$.
- The referee's minor points. (m1) DOM$`^{\mathrm{rel}}`$ is used for the region restarts of leaves read by $`\Theta`$ and of closure parameters, which are not nodes of the pin tree; the fix: every code of the
  finite pattern is below $`m_\lambda`$, so $`\beta_\lambda`$ is chosen over the whole pattern before $`\kappa_0`$; two side statements of DOM$`^{\mathrm{rel}}`$ are wrong and unused. (m2) The special form of
  LONG-CLASS$`^\omega`$ used for NU-LOW″⁺ ("$`r(\lambda) \ge H(\eta_\lambda + G(\theta_k\cdot\omega^2))`$ gives $`m_\lambda \ge G(\theta_{k+1}\cdot\omega^2)`$") needs $`R(\zeta) \lt G(\theta_k\cdot\omega^2)`$ for every $`\zeta \lt \theta_{k+1}\cdot\omega^2`$, which is stated
  but not proved anywhere (an earlier referee accepted it; the referee's test found 0 failures; now proved twice, §2.1, §2.2). (m3) At level 2, $`\kappa_0 \ge \max(m^*, H(z_0))`$ must be required. (m4) Two citations are too broad.
  (m5) One cited lemma is labelled with LOW$`^\infty`$; only its argument is used, which the paper should say since it derives not-LOW. (m6) Two statements are made for every offset but proved
  only under the coverage of (m1).

### 1.2 $`\nu_C = \nu_S`$: TC⁺ at the codes of B-1, exact reaches below $`G(\hat\zeta_{23})`$, and REDUCTION$`^{(6)}`$

Notation of [SHIFT5.md](SHIFT5.md) §2.2 and [SHIFT6.md](SHIFT6.md) §1.2; LOW$`^\infty`$ is $`\nu_C \lt \upsilon^\infty`$.

- **The minor points of the reviews of [SHIFT6.md](SHIFT6.md) §2.2, §3.1 and §3.2 are applied** (**2 reviews**; wording and citations, a withdrawn remark, the Lean mirror of the order facts).
- **EQ-F$`^B`$** (proved, without FRAG). For every base change $`B`$ of the known kind and every short code $`c`$ at a restart $`\nu'`$ of its domain, $`B(\mathrm{cl}_{\nu'}(c)) = \mathrm{cl}_{B\nu'}(c^B)`$. The proof
  applies the reading lemma at the code $`c`$ itself, so the domain question of [SHIFT6.md](SHIFT6.md) §3.1 does not come up.
- **EQUIV$`^B`$** (proved by transfer): the landing data commute with $`B`$. **TC⁺ at the codes of B-1** (proved, given FRAG), for example at $`G(\Omega_3) + P`$, and TC⁺ for every code that has an exact
  landing theorem. So the step that [SHIFT6.md](SHIFT6.md) §3.1 found missing is proved, and REDUCTION$`^{(5)}`$ of [SHIFT6.md](SHIFT6.md) §2.2 is now proved (as a reduction).
- **FAR-PIN$`^{L5}`$** (proved by transfer, given FRAG): the relative pins of [SHIFT6.md](SHIFT6.md) §1.2 for every long code below $`\varepsilon_{G(\hat\zeta_G)+1}`$, whose landings have prefix codes at most $`\hat G`$.
  (The referee, minor: one more place uses the bound of the old range, an image that absorbs the landing when the first landing exponent is above $`G_2`$, as on the $`\varepsilon`$ tier and at
  $`G(\hat\zeta_3\cdot 2)`$; the referee gives a short repair with existing tools, from the cap at the code of the image.)
- **PREFIX-BOUND** (proved, checked). Every landing prefix code of a code below $`G(\hat\zeta_{23})`$ is below $`\varepsilon_{G(\hat\zeta_G)+1}`$, because $`R(\hat\zeta_{23}) = \varepsilon_{G(\hat\zeta_G)+1}`$. So $`G(\hat\zeta_{23})`$ is the first code that
  needs a relative pin at a code $`\ge \varepsilon_{G(\hat\zeta_G)+1}`$.
- **STAGE-1, RP-STEP** (proved by transfer, given FRAG, after the repair of the minor point above, which matters from the code $`G(\theta_4\cdot\omega^2 + \hat\zeta_G)`$ on). Exact two-sided reaches for every long
  code below $`G(\hat\zeta_{23})`$, at every level (among them $`[G(\hat\zeta_3+\Omega_2), G(\hat\zeta_A))`$, the family $`\hat G`$ past its $`\varepsilon`$ tier, and the hull families, where the hull caps are attained), and the
  relative pins for every code below $`G(\hat\zeta_{23})`$ (**2 reviews** at levels 1 and 2, with §1.1).
- **(R2‴), (R5′)** (proved under LOW$`^\infty`$, given FRAG). CAP-0 below $`G(\hat\zeta_{23})`$ gives small span bottoms, room and domain up to $`G(\hat\zeta_{23})`$; zones with tops $`G(\hat\zeta_{G4} + t_n) \to G(\hat\zeta_{23})`$
  ($`\hat\zeta_{G4} = \theta_4\cdot\Omega_4`$) are zone systems with no further hypothesis, which replaces the conditional zones of [SHIFT6.md](SHIFT6.md) §1.2.
- **REDUCTION$`^{(6)}`$** (proved, as a reduction). $`\nu_C = \nu_S`$ follows from FRAG, LOW$`^\infty`$ and three pieces, all at codes $`\ge G(\hat\zeta_{23})`$: (R1$`^{(6)}`$) exact reaches that can be pinned, in
  blocks of spans and in zones; (R2$`^{(6)}`$) caps, room and domain for codes and offsets; (R5$`^{(6)}`$) zones past $`H(\eta_x + G(\hat\zeta_{23}))`$. The relative pin is no longer a separate piece below
  $`G(\hat\zeta_{23})`$. Whether the pins of §1.1 (levels 1 and 2, codes below $`P'`$) fill part of this residue is not checked by a referee.
- **Not proved** (blocking point of the referee): STAGES, which iterates STAGE-1 along thresholds that tend to $`P'`$. It extends the practice for uncountable η-offsets from offsets below
  $`\varepsilon_{G(\hat\zeta_G)+1}`$ to offsets below $`P'`$ in one sentence, and names no base whose $`\pi`$ is above the threshold. So its corollaries in this paper (CAP-0 below $`P'`$, not-LOW), the zones up to
  $`H(\eta_x + P')`$ and REDUCTION$`^{(6)+}`$ are not proved here (CAP-0 below $`P'`$ and not-LOW are proved in §1.1 by another route). $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$ are both **open**.
- The referee's other minor points: one continuity claim is cited from a lemma that does not state it (use the named restart of the landing calculus); one lemma is said to apply "verbatim" where the
  range is covered only by an accepted remark; the corollary of STAGES must be labelled conditional.

### 1.3 Native codes: stage labels of every finite level, and the start of the ω-top (one blocking point, repaired by the referee)

Words of [SHIFT6.md](SHIFT6.md) §1.3 and §3.3. A stage label $`T`$ has level $`l`$ when $`\Omega_l \le T \lt \Omega_{l+1}`$.

- **The minor points of the review of [SHIFT6.md](SHIFT6.md) §3.3 are applied** (**2 reviews**): the meaning of "a code over $`X`$" in TOP-HOST$`^q`$, the number of roots of rule R3, the certificates of the
  new copy rule, the corollary that the point of the top for the argument 0 is above $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$, and that no upper bound is known.
- **PREFIX⁺, GOOD, D-GOOD** (proved). If $`\psi_{\Omega_j}(\beta)`$ is a normal form, so is $`\psi_{\Omega_j}`$ of every leading CNF part of $`\beta`$. Every point $`\eta = \Omega_\omega\cdot\xi + \eta'`$ of $`D`$ has a good stage $`1+\xi`$
  (one where $`\psi_{\Omega_2}(\Omega_\omega\cdot(1+\xi))`$ is a normal form). Bad stages exist (every stage in $`[\sigma_2, \Omega_2)`$), but they occur only as ordinary indices.
- **(PL), INNER-PAIR** (proved): primitives are used only at the levels above the level of the label; at the lower levels the stage atoms are ordinary ϑ-atoms.
- **PT-blocks, SCOPE, LABEL-ORDER, SHAPE$`^q`$, PAIR-DOWN for sums** (proved), **ROW$`^q`$, TOP-HOST$`^q`$** (proved by transfer). A block refers to its label in the row of the label's own level:

```math
g \lt a \lt_2 b,\qquad a \le_1 b + V_l(T),\qquad g \le_1 b + g + V_j(\beta).
```

  The label values increase strictly with the label, every code is a fan-free pattern with chain number 2, and the one top (a pair with $`a \le_1 b\cdot 2`$) hosts every finite level.
- **Not proved as written** (blocking point B-1 of the referee): **MIN-A0** (at a visible level the end point is the least element of its C-set). The proof writes an arbitrary ordinal $`\gamma`$ as
  $`\psi_{\Omega_j}(d)`$, but the Lean theorem it quotes (`Term.existsUnique_NF`) holds only for values of terms, a countable set, while the end point is a minimum over all ordinals. The referee gives a repair
  (a descent through the constants of the argument down to a subterm all of whose constants are below $`\gamma`$) and checked it in full; the repair has had no second check, so it is **not counted yet** (the second check came in §2.3, and these results now count).
  The results that rest on MIN-A0 are proved once the repair is accepted, and are **not counted yet**: LIM$`^K`$ at the visible levels, STAGE$`^{(l)}`$ and PUSH$`^S_l`$ for every finite $`l`$, IDX$`^q_l`$, the ω-top stages
  $`\Omega_\omega\cdot\vartheta + \tau`$ with $`\vartheta \lt \omega^\omega`$ (LIM$`^\omega`$, STAGE$`^\omega`$, LEX-ORDER, IDX$`^\omega_k`$), and natively

```math
\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_l)\ (\text{every } l),\qquad \iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega^2),\qquad \iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega),
```

  with RED-TOWER for the one chain number 3 below the last bound. The counted bound stays $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$ ([SHIFT6.md](SHIFT6.md) §3.3). These are lower bounds only;
  no upper bound for $`\iota(\mathrm{CH}_3)`$ is known.
- **Open**: $`\vartheta \ge \omega^\omega`$ (the free levels run out), $`\vartheta`$ of level $`\ge 1`$ (two label values in one block), labels of level $`\omega`$ ($`\Omega_{\omega+1}`$), $`\Omega_{\omega\cdot 2}`$, and on to $`\theta_0`$.
- The referee's other minor points: the same gap as B-1 is in an earlier cited step of the counting rule (one case) and is repaired by the same descent; one side remark about levels is false
  for ω-top stages and unused; one pattern has 10 elements, not 12; the range of one lemma should be in its statement.

### 1.4 Status after the thirtieth round

Superseded by §2.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, L(\omega+1)]`$ given FRAG ($`[0, X_{21}]`$ with 2 reviews; up to $`X_{23}`$ with 1 review of the repair of B-1; up to
  $`L(\omega+1)`$ with 1 review, §1.1). The core half holds on $`[0, \nu_C]`$. No InaccPsi upper bound for $`\nu_C`$: (P) and (Q′) at $`(L(\omega), L(\omega+1))`$ stay open.
- Reaches (given FRAG): exact for every short restart with $`\tau \lt G_2`$ and every long restart with code below $`P'`$ at levels 1 and 2 (below $`G(\hat\zeta_3)`$ 2 reviews; below $`G(\hat\zeta_{23})`$ 2 reviews at
  levels 1 and 2, and at every level 1 review); relative pins at every depth for the codes below $`P'`$ at levels 1 and 2. CAP-0 for every code below $`P'`$, and CAP-1.
- **LOW: false, given FRAG** ($`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$; 1 review).
- Names: no change. The lower-bound program below $`\theta_0`$: the counted native bound stays $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$; the bounds up to $`\psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega)`$
  wait for the check of the referee's repair (§1.3). The step below SRO: no change (every $`n`$ on all 3,166 sample matrices; the general statement is open).
- $`\nu_C = \nu_S`$: open; REDUCTION$`^{(6)}`$ leaves LOW$`^\infty`$, (R1$`^{(6)}`$), (R2$`^{(6)}`$), (R5$`^{(6)}`$).

### 1.5 Checks of the thirtieth round

Each run was under 60 seconds; none is a proof.

- §1.1. Pin trees of 791 constant-free multipliers (two seeds; 1,759 nodes, depth at most 2): the codes decrease strictly, the landing inclusion holds at every depth, and the bound holds, 0
  failures; the witnesses match the earlier calculus; the chain $`L(1) \lt L(\omega) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + \omega^{\mathbb{G}^\vartheta+1}) \lt L(\omega+1) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ and the normal form of $`L(\omega+1)`$, in Python
  and Lean (green, identical). The referee: new seeds 7 and 8 (375 and 400 multipliers, 812 and 883 nodes, also the long exponents in $`[G_2, \hat G)`$ that the author's test skips), 0 failures; the
  special form of LONG-CLASS$`^\omega`$ on 74, 268 and 375 codes ($`k = 2, 3, 4`$), 0 failures; the reruns identical. Not testable here: everything with constants, where the hypothesis on the
  hereditary parameters is not empty.
- §1.2. Ten runs on the ordinal side (orders and readings, the bound on landing prefix codes, the zone tops and bases), 0 failures; Lean green, identical to Python. The referee: the thresholds of
  STAGES and 13 multipliers at depth 2, 0 failures; the witnesses of the absorption case; the prefix bound on 152 multipliers near $`\hat\zeta_{23}`$, 0 failures; the Lean rerun identical.
- §1.3. Names and memberships (two seeds), 0 failures; Lean green, identical to Python; 24 new codes and tops are fan-free patterns with chain number 2, and a mutant has chain number 3.
  Certificates (replayed): forward 17 of 21, reverse 0 of 7. The referee: new seeds, 0 failures; own tests of GOOD on 490 stages and 6,123 pairs, of "every stage in $`[\sigma_2, \Omega_2)`$ is bad" on 792
  stages and of PREFIX⁺ on 4,761 pairs, 0 failures; two nested self-labels give valid patterns with chain number 2; 4 of 4 predicted certificates found, among them both cross-level cases
  of LEX-ORDER; 0 of 7 predicted-false found within 45 seconds each ("not found" is not a disproof); the Lean rerun identical.

### 1.6 Open

Superseded by §2.6.

- Upper bounds: (P) and (Q′) at $`(L(\omega), L(\omega+1))`$ for $`\nu_C \le L(\omega+1)`$, the upper half of the conjectured name. (P) needs the reaches at the code $`P'`$ at level 2 (the restarts of code $`P'`$ across
  the offset $`\omega^{P'+1}`$); (Q′) needs the isominimal patterns of $`L(\omega)`$. Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The claim above $`L(\omega+1)`$ given FRAG: first $`\nu_C \le L(\omega+1)`$ (then the claim holds on $`[0, \nu_C]`$), then the levels above $`\nu_C`$; the calculus for codes $`\ge P'`$ at level 2 and above.
- The first inaccessible: a second check of the referee's repair of MIN-A0 (then $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega)`$ counts); $`\vartheta \ge \omega^\omega`$; $`\vartheta`$ of level $`\ge 1`$; labels of level $`\omega`$,
  $`\Omega_{\omega\cdot 2}`$, and on to $`\theta_0`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW$`^\infty`$; (R1$`^{(6)}`$), (R2$`^{(6)}`$), (R5$`^{(6)}`$) at codes $`\ge G(\hat\zeta_{23})`$ (or STAGES with the η-offset step written out); then (D1b) and (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`L(\omega+1)`$ for the points that are not
  $`\upsilon`$-points; the rest of [COVER.md](COVER.md) §9.

## 2. The thirty-first round

Three papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means, as in §1, that a referee of the
thirtieth round asked for the change and a referee of this round checked it, or that two papers of this round prove the result independently and both referees found it
proved. None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this). Papers cited: in §2.1 only through
refereed steps of earlier rounds ([W07b] L.2.1; Carlson, "Patterns of resemblance of order 2" (2009), L.5.5 and L.5.7; Wilken, "A glimpse of Σ₃-elementarity" (2020), L.21.7 and
Prop. 21.11); in §2.2 [W07b] L.2.1 and Carlson (2009), Thm 14.14 (the core of $`R_2`$, with $`+`$, is an initial segment; the referee checked it against the paper); no paper is used in a
proved step of §2.3, which does not use FRAG. No Lean file was added: each paper checked its ordinal inputs with a Lean file that only compares terms (`#eval`, no theorem;
green, and identical in the referee's rerun); these count as checks. Levels are numbered as in §1 (one higher than in the papers). Write $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$,
so $`L(\xi) = H(\Omega_\omega + P'\cdot\xi)`$ and $`m^* = L(0)`$.

### 2.1 $`\nu_C = \nu_S = L(\omega+1)`$, given FRAG: Wilken's claim holds in $`R_2^C`$ on $`[0, \nu_C]`$

- **The minor points of the review of §1.1 are applied** (**2 reviews**). DOM$`^{\mathrm{rel}}`$ is restated for every long code of the finite pattern (also the region restarts of leaves read by $`\Theta`$
  and of closure parameters), with $`\beta_\lambda`$ chosen over the whole pattern before $`\kappa_0`$; the two wrong side statements are deleted; at level 2, $`\kappa_0 \ge \max(m^*, H(z_0))`$; the citations and the
  label of the reused lemma are corrected.
- **LC-STRICT** (proved). For $`k \ge 3`$ and every code $`D' \lt G(\theta_{k+1}\cdot\omega^2)`$ (at every level):

```math
R_u(D') \lt G(\theta_k\cdot\omega^2),\qquad \Lambda(D') + \omega^2 \lt G(\theta_k\cdot\omega^2),
```

  and the same with $`G_2`$ in place of $`G(\theta_2\cdot\omega^2)`$. So every restart $`\lambda`$ with code below $`G(\theta_{k+1}\cdot\omega^2)`$ has $`r(\lambda) \lt H(\eta_\lambda + G(\theta_k\cdot\omega^2))`$. This proves the step that
  the minor point (m2) of §1.1 found stated but not proved, so the lower half $`\nu_C \ge L(\omega+1)`$ of §1.1 no longer rests on a numeric check. The paper of §2.2 proves the same step
  independently (LONG-CLASS$`^\Omega`$), so the repair has **2 reviews**. The referee (minor): the proof needs $`\Theta(G(\theta_{k+1}\cdot\omega^2)) = H(\eta + G(\theta_k\cdot\omega^2))`$, which follows from the
  reading formula of THETA$`^w`$ and the closed form of the reading $`R(\theta_{k+1}\cdot\omega^2) = G(\theta_k\cdot\omega^2)`$; the cited step of an earlier paper is in a part that §1.1 does not use.
- **CROSS-LIM** (proved by transfer, given FRAG). A restart $`\lambda`$ with code $`m_\lambda \ge P'`$ and $`e_\lambda \ge P'`$ reaches $`H(\eta_\lambda + P')`$ (when that point is at most $`\nu_S`$). The proof runs the crossing
  step of the exact calculus with realizers of every constant-free code $`G(\theta_{k+1}\cdot\omega^2) \lt P'`$ (they lie cofinally below $`\rho_\lambda`$), and closes, since $`H(\eta_\lambda + P') = \sup_k H(\eta_\lambda + G(\theta_k\cdot\omega^2))`$.
  The code of $`\lambda`$ itself is never read. Hence, for every $`n \lt \omega`$:

```math
L(n) \le_1 L(n+1),\qquad L(n) \le_1 L(\omega),\qquad L(\omega) \le_1 L(\omega+1).
```

  The referee: proved at $`L(n)`$ for $`n \ge 1`$ and at $`L(\omega)`$. At $`m^* = L(0)`$ the step mixes two levels ($`m^*`$ is at level 2, its realizers at level 1), which only a remark of an earlier
  round covers; this case is used only for $`r(m^*)`$ and $`m_0 = m^*`$ below, not for PAIR, UP or NU (minor m1).
- **TC⁺$`^\omega`$, EMB, ONTO-FIN** (proved by transfer, given FRAG). Let $`B_n`$ be the η-base change that maps $`L(n)`$ to $`L(\omega)`$ and fixes $`[0, L(n))`$. For every restart $`R`$ of the gap
  $`[L(n), L(n+1))`$, $`r(B_n R) = B_n(r(R))`$: the exact calculus at level 2 and EQUIV$`^{\mathrm{rel}}`$ (§1.1), applied to a base change under which codes grow. $`B_n`$ restricted to $`[0, L(n+1))`$ is an
  embedding of $`R_2^S`$ (it keeps $`0`$, $`+`$, $`\lt`$, $`\le_1`$, $`\le_2`$) into $`[0, L(\omega+1))`$, and every finite $`Y \subseteq [L(\omega), L(\omega+1))`$ lies in its image for every large $`n`$. The referee's minor points: the
  gap $`[m^*, L(1))`$ ($`n = 0`$) is used once and needs only the calculus (m2); one case of $`\le_2`$ in EMB must use the map on the offsets, since at the base the code changes from $`P'`$ to $`P'+1`$ (m3);
  the paper should say that EQUIV$`^{\mathrm{rel}}`$ uses neither CODE-MON nor reaches, and how the supremum at the image is evaluated (m5); its own order test covers only some atoms (m6).
- **PAIR, UP, NU** (proved, given FRAG). The three statements above are exactly the hypotheses of the shift criterion SHIFT ([SHIFT.md](SHIFT.md) §1, refereed) with $`a = L(\omega)`$, $`b = L(\omega+1)`$ and
  $`c_n = L(n)`$ (the referee checked them against its exact statement, "$`c_{n+1} \le_1 a`$ for every $`n`$" included). So $`L(\omega) \lt_2 L(\omega+1)`$ in $`R_2^S`$ (PAIR), and $`\nu_C \le \nu_S \le L(\omega+1)`$ (UP; this half uses
  neither the lower half nor not-LOW). With the lower half of §1.1 and LC-STRICT:

```math
\nu_C = \nu_S = L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P').
```

  **Milestone: Wilken's claim holds in $`R_2^C`$ on $`[0, \nu_C]`$ (given FRAG)**, both halves: the core half because $`[0, \nu_C]`$ lies in the core ([BREAK.md](BREAK.md) §2), the names half because
  $`\nu_C = L(\omega+1)`$ is a normal form (Lemma L). Also $`\nu_C = \nu_S`$: $`R_2^C`$ has no ghost pair, which settles the first case of $`R_2^S = R_2^C`$. The upper half has 1 review; the lower half has
  1 review (§1.1), and the repair of its one gap has 2.
- **NU-NAME in full** (proved, given FRAG). The left end of the first nested pair is $`a_0 = x = L(\omega)`$, its $`\le_1`$-predecessors at level 2 are the points $`L(n)`$, and $`m_0 = m^*`$; so the conjecture
  NU-NAME ([BREAK.md](BREAK.md) §2, §8) holds. Reaches: $`\mathrm{lh}(L(\omega)) = r(L(n)) = L(\omega+1)`$ for $`n \ge 1`$, and $`r(m^*) = L(\omega+1)`$ ($`r(m^*)`$ and $`m_0 = m^*`$ rest on the case m1 above). Every restart below
  $`\nu`$ now has an exact reach.
- **(P), (Q), (Q′), NU-MIN** (proved, given FRAG). (P) holds at $`(L(\omega), L(\omega+1))`$ by CROSS-LIM; (Q) and (Q′) follow from PAIR and the cap lemma of the fan program ([BREAK.md](BREAK.md) §2), not
  from a reach computation: in the case $`\nu_C \gt L(\omega+1)`$, CROSS-LIM would give $`r(L(\omega)) \gt L(\omega+1)`$, so no computation of reaches alone could prove (Q). NU-MIN is attained at $`a = L(\omega)`$.
- **LOW$`^\infty`$** (proved, given FRAG): $`\nu_C \lt \upsilon^\infty`$, from UP.
- **Not proved** (open): the claim above $`\nu_C`$, where the structure is not skeletal (the pairs of level 2 and up, the fans); $`R_2^S = R_2^C`$ above $`\nu`$; the core half in $`R_2^S`$ above $`\upsilon_{\omega^3}`$.
- The referee checked the hypotheses of the steps that rest on the calculus at level 2 and on EQUIV$`^{\mathrm{rel}}`$ (re-runs of refereed proofs), but did not re-derive those proofs line by line; the
  points to check first are the realizer step of CROSS-LIM, EQUIV$`^{\mathrm{rel}}`$ for $`B_n`$, and the $`\le_1`$ cases of EMB.

### 2.2 The residue of $`\nu_C = \nu_S`$ below $`P'`$, LOW$`^\infty`$, and REDUCTION$`^{(7)}`$ (superseded by §2.1)

- **The minor points of the review of §1.2 are applied** (**2 reviews**), and the blocking point of STAGES (§1.2) is answered without STAGES: the place list it asked for is the one of the relative far
  pin of §1.1 at level 1, and at level 2 and above $`\beta = \Omega_\omega`$ works, since $`\pi_\eta \ge P'`$ for every $`\eta \ge \Omega_\omega`$. The referee: proved as cited; STAGES itself stays not proved; one case (near pins at
  short uncountable exponents) uses the practice that the blocking point objected to, and the paper should say why it is valid there (minor m1).
- **FAR-PIN$`^{L,\mathrm{lev}}`$** (proved by transfer, at the level of an inventory, given FRAG; minor m2): the results of §1.1 at every level $`\ge 2`$, with $`\kappa_0 \ge \max(m^*, H(z_0))`$.
- **LONG-CLASS$`^\Omega`$** (proved, given FRAG): $`r(\lambda) \ge H(\eta_\lambda + G(\Omega_k))`$ gives $`m_\lambda \ge G(\Omega_{k+1})`$ ($`k \ge 3`$). This is the second independent repair of (m2) of §1.1 (see LC-STRICT). The
  referee (minor m3): one line for the segments below $`\theta_2`$ is missing; it is true.
- **CAP-EXP, LOW-FACTS$`^\omega`$, SPAN, ROOM, DOMAIN, zones** (proved under LOW$`^\infty`$, given FRAG): the points $`u_n`$ and $`x`$ of the fan program have codes $`\ge P'`$; span bottoms, room and domain
  up to $`P'`$; zones with tops $`H(\eta_u + G(\Omega_k))`$, cofinal in $`H(\eta_x + P')`$ (minor m4: cite the continuity of $`H`$ there). **REDUCTION$`^{(7)}`$** (proved, as a reduction): $`\nu_C = \nu_S`$ follows from FRAG,
  LOW$`^\infty`$ and two placement pieces at codes $`\ge P'`$.
- **LOW-COND, NECESSITY** (proved): $`\nu_C \le L(\omega+1)`$ implies $`\nu_C \lt \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ and so LOW$`^\infty`$; the upper half of Wilken's claim in $`R_2^C`$ implies LOW$`^\infty`$ (with Carlson 2009,
  Thm 14.14), so the failure of LOW$`^\infty`$ would refute it (minor m6: LOW$`^\infty`$ also keeps the points and chains below $`\upsilon^\infty`$). **P-LOW$`^\omega`$** (proved for a restart $`a`$, given FRAG; not proved for
  every pair of the form CPB-S of [SHIFT.md](SHIFT.md) §1, minor m5): in such a pair a final segment of the predecessors that (P) needs have codes $`\ge P'`$, so no statement about codes below $`P'`$ alone bounds $`\nu_C`$.
- **Superseded.** §2.1 proves LOW$`^\infty`$ and $`\nu_C = \nu_S`$ by another route, so REDUCTION$`^{(7)}`$ and its two pieces are no longer needed. This paper itself left $`\nu_C = \nu_S`$ open; it adds to
  the count only LC-STRICT's second review and the lemmas above.

### 2.3 Native codes: MIN-A0 for every ordinal, and the ω-top up to $`\varepsilon_{\Omega_\omega+1}`$

- **The minor points of the review of §1.3 are applied** (**2 reviews**).
- **BELOW-γ, DESCENT, MIN-A0** (proved, given the counting rule PSI-n and CNST$`^n`$ of [SHIFT3.md](SHIFT3.md) §2.1). Let $`G = \psi_{\Omega_{j+1}}(B)`$ and let $`\gamma`$ be any ordinal in $`R^j_G`$ with
  $`\Omega_{j-1} \lt \gamma \lt \Omega_j`$. Every normal form $`d \lt B`$ whose constants are below $`\gamma`$ has $`\psi_{\Omega_j}(d) \lt \gamma`$ (BELOW-γ); a constant of $`B`$ that is $`\ge \gamma`$ leads to a subterm $`\psi_{\Omega_j}(e^*) \ge \gamma`$ with
  $`e^* \lt B`$ and all constants of $`e^*`$ below $`\gamma`$ (DESCENT). So $`R^j_G \cap (\Omega_{j-1}, \psi_{\Omega_j}(B))`$ is empty for all ordinals, not only for the values of terms. This is a second proof of the referee's
  repair of the blocking point B-1 of §1.3, checked by another referee, so **MIN-A0 has 2 reviews**, and the results of §1.3 that rest on it count now:

```math
\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_l)\ (\text{every } l),\qquad \iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega^2),\qquad \iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega).
```

  The same lemma removes the step through the values of terms from one case of the proof of PSI-n. The referee (minor m1, m2): a stage label is an arbitrary ordinal, so the descent
  should end with a lemma ONTO$`^{\mathrm{ord}}`$ (every strongly critical $`y`$ with $`\Omega_{j-1} \lt y \lt \psi_{\Omega_j}(\beta)`$ is $`\psi_{\Omega_j}(d)`$ for a normal form $`d \lt \beta`$), which the referee proves by a short descent from
  facts that are in Lean; it also closes the last step of PSI-n that used the values of terms, and makes the first proof of MIN-A0 valid too.
- **The ω-top up to $`\varepsilon_{\Omega_\omega+1}`$** (proved; the last steps by transfer). A stage $`\Omega_\omega\cdot\vartheta + \tau`$ with $`\vartheta \lt \varepsilon_{\Omega_\omega+1}`$ is coded by a pair-free region above $`b`$ whose units are
  decorations $`e \le_1 \mathrm{val}_e(\gamma+1) + \lambda(x)`$, one for each weight $`\Omega_\omega\cdot\gamma + x`$ of $`\vartheta`$ (the label $`x`$ of any finite level, and $`\gamma`$ coded by a nested region). Each label gets its own
  decoration, so no reach end carries two label values; this covers $`\vartheta \ge \omega^\omega`$, $`\vartheta`$ of every finite level, and multipliers of $`\Omega_\omega`$ (WT$`^L`$, SUP$`^L`$, REGION$`^L`$, MAJ, LEX$`^R`$, SHAPE$`^R`$,
  PAIR-DOWN$`^R`$, TOP-HOST$`^R`$, IDX$`^R`$, STAGE$`^\varepsilon`$, PUSH$`^\varepsilon`$). The codes keep chain number 2, so natively

```math
\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1}),
```

  past $`\psi_{\Omega_1}(\Omega_\omega^2\cdot\varepsilon_0)`$, $`\psi_{\Omega_1}(\Omega_\omega^3)`$, $`\psi_{\Omega_1}(\Omega_\omega^\omega)`$ and $`\psi_{\Omega_1}(\Omega_\omega^{\Omega_\omega})`$, and RED-TOWER holds with $`\mathrm{CH}_3`$ for every $`t \lt \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$. This refutes the first part of an
  earlier conjecture, that the chain number must grow without bound below $`\varepsilon_{\Omega_\omega+1}`$. These are lower bounds only; no upper bound for $`\iota(\mathrm{CH}_3)`$ is known.
- The referee's other minor points: PUSH$`^\varepsilon`$ needs an infinite $`S`$ (m3); the hypothesis of REGION$`^L`$ is needed only for the label pairs that are compared (m4); wording (m5); the least checked
  case is a label decoration copied under a decoration with $`\gamma \ge 1`$, where every certificate search timed out and only the proof covers it (m6).
- **Open**: $`\varepsilon_{\Omega_\omega+1}`$ itself and the Veblen functions over $`\Omega_\omega`$; labels of level $`\omega`$ (they need a row of level $`\omega`$, which a finite code does not have; that they reach
  $`\psi_{\Omega_1}(\Omega_{\omega+1})`$ is a conjecture); $`\Omega_{\omega\cdot 2}`$, and on to $`\theta_0`$.

### 2.4 Status after the thirty-first round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, \nu_C]`$ given FRAG, with $`\nu_C = \nu_S = L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P')`$** ($`[0, X_{21}]`$ with
  2 reviews; up to $`L(\omega+1)`$ the lower half with 1 review, §1.1, and its repair with 2, §2.1, §2.2; the upper half with 1 review, §2.1).
- $`R_2^S`$ against $`R_2^C`$: $`\nu_C = \nu_S`$ given FRAG (no ghost, 1 review); $`R_2^S = R_2^C`$ above $`\nu`$ is open.
- Reaches (given FRAG): exact for every restart below $`\nu`$; $`\mathrm{lh}(L(\omega)) = r(L(n)) = L(\omega+1)`$.
- **LOW: false, given FRAG** (1 review, §1.1). **LOW$`^\infty`$: true, given FRAG** (1 review, §2.1).
- Names (given FRAG): $`\nu = L(\omega+1)`$, $`a_0 = L(\omega)`$, $`m_0 = m^*`$ (the last rests on the minor point m1 of §2.1). The lower-bound program below $`\theta_0`$: counted native bounds
  $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega)`$ (MIN-A0 with 2 reviews) and $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ (1 review). The step below SRO: no change (every $`n`$ on all 3,166 sample
  matrices; the general statement for all standard matrices below SRO is open).

### 2.5 Checks of the thirty-first round

Each run was under 60 seconds; none is a proof.

- §2.1. The names, the memberships of CROSS-LIM and the chain $`L(0) \lt L(1) \lt \dots \lt L(\omega) \lt L(\omega+1)`$; $`B_n`$ on 98 offsets with moved atoms, the order kept on 2 × 4,704 pairs; LC-STRICT on 2 × 939
  cases; all 0 failures; Lean green, identical to Python. The referee: the reruns identical; an own test of $`B_n`$ with atoms that are not $`\upsilon`$-points, offsets with two atoms, offsets outside
  $`D`$ and fixed atoms in $`[L(1), L(2))`$, 1,085,970 ordered pairs, 0 failures; the realizer targets of CROSS-LIM lie below $`\lambda`$, 36 of 36.
- §2.2. LONG-CLASS$`^\Omega`$ on 867 multipliers, the base $`\Omega_\omega`$ with a negative control, and LOW-COND, 0 failures. The referee: 369 multipliers near the top of each level up to $`\Omega_7`$, 0
  failures; 10 bases with countable constants at high levels, with a negative control that fails as expected; the chain constants; the reruns byte-identical; the Lean file of §1.1 rerun green.
- §2.3. 118 checks of the names on each of 2 seeds, 0 failures; Lean green, identical to Python; 23 new codes and tops are fan-free patterns with chain number 2, and both mutants have
  chain number 3. Certificates (replayed): forward 15 of 17, tops 6 of 8, reverse 0 of 7; the 4 not found timed out at 54 seconds ("not found" is not a disproof). The referee: a new seed, 0
  failures; an own checker of the regions on about 6,600 random pairs, 0 failures; extra certificate searches, forward 1 of 3 found, reverse 0 of 4; the Lean rerun identical.

### 2.6 Open

- The claim above $`\nu_C = L(\omega+1)`$ given FRAG (above $`X_4`$ without FRAG). Above $`\nu`$ the structure is not skeletal: the pairs of level 2 and up, the fans, toward $`\theta_0`$; the calculus for codes
  $`\ge P'`$ at level 2 and above; in $`R_2^S`$, $`o_k = \omega`$ for the levels above $`\nu`$, the reaches of their restarts, and their names (conjecture: $`\psi_{\Omega_1}(\Omega_\omega\cdot k)`$,
  $`\psi_{\Omega_1}(\Omega_\omega\cdot k + \omega^{P_k+1})`$, $`\psi_{\Omega_1}(\Omega_\omega\cdot k + \omega^{P_k+1} + P_k)`$ with $`P_k = \psi_{\Omega_2}(\Omega_\omega\cdot k)`$). The crossing at $`m^*`$ across two levels as its own step (minor m1 of §2.1).
- $`R_2^S = R_2^C`$ above $`\nu`$; the core half in $`R_2^S`$ above $`\upsilon_{\omega^3}`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: $`\varepsilon_{\Omega_\omega+1}`$ itself and the Veblen functions over $`\Omega_\omega`$; labels of level $`\omega`$ ($`\Omega_{\omega+1}`$), $`\Omega_{\omega\cdot 2}`$, and on to $`\theta_0`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$;
  the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names above $`\nu`$ for the points that are not
  $`\upsilon`$-points; the rest of [COVER.md](COVER.md) §9.
