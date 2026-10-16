[← Back](README.md) | [English](AUDIT.md) | [Japanese](AUDIT-ja.md)

# $`R_2^+`$: the dependency table of $`\nu_C = L(\omega+1)`$ (the audit of the thirty-second round)

This page belongs to [SHIFT7.md](SHIFT7.md) §3.1; the rows T2b2 and T2c1 and the last section are updated by the thirty-third round ([SHIFT8.md](SHIFT8.md) §1.2) and the thirty-fourth round (§2.1 there). It lists what the milestone of [SHIFT7.md](SHIFT7.md) §2.1 rests on:

```math
\nu_C = \nu_S = L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P'),\quad\text{and Wilken's claim in } R_2^C \text{ on } [0, \nu_C]\quad(\text{given FRAG}).
```

The table is the audit's, with the corrections of the audit's referee (R-1 for T2b2, R-3 for S12). The status words are those of [README.md](README.md) §3; "transfer" means proved by
re-running a refereed proof with the changes written out. "Reviews" counts the independent reviews after the thirty-second round. The audit re-derived the nodes marked "audit" line by
line, and its referee agreed, so each of them has one review more than before; the audit checked every other node only for its place, its label and its hypotheses. Levels are numbered as
in [SHIFT7.md](SHIFT7.md) (one higher than in the papers). "Given FRAG" means given FRAG with FRAG-SUBST, SUBST-COMM and the own proof of [W07b] Thm 2.2.

**Verdict of the audit**: no fatal and no blocking point; the milestone holds at the standard "proved by transfer"; all findings are minor (text, scope, citations).

**Later (the fortieth round, [SHIFT10.md](SHIFT10.md) §3.2):** a second audit and two referees found that the chain uses exact long reaches at codes where the old value is false (every $`m_0 \ge \Omega_1`$, for example the code $`G_2 + P`$ that CROSS-LIM crosses, and the landing for $`2 \le D \lt \hat G`$). So **T0 is not proved as written**, and so are the rows marked so below; the verdict above is superseded. The rows that use no exact long value at an affected code stand. FRAG (S13) and FRAG2 (S15) are now also proved in Lean from 20 cited facts ([LEAN.md](LEAN.md)).

**Later (the forty-first round, [SHIFT11.md](SHIFT11.md) §1.1):** the corrected exact long reach is proved for every code below $`P'`$ at levels 1 and 2 (ENUM-REACH), and the chain was run again on it. So **T0 is proved again** (given FRAG; 1 review of the new proof), and so are the rows marked "not proved as written (fortieth round)" below, as the table of the forty-first round at the end of this page says. The rows S1 and S2 are replaced by ENUM-REACH.

**Later (the forty-second round, [SHIFT11.md](SHIFT11.md) §2.1):** the step TC⁺$`^\omega`$ for $`B_n`$ (T2c) now cites EQ$`^{\mathrm{all}}`$, so T0 is complete as written; and the gap calculus above $`\nu_C`$ is run again, so the frontiers up to $`Z^\Lambda`$ are proved again (the table of the forty-second round at the end of this page). **Later (the forty-third round):** the claim goes on to $`Z^{\mathrm{FP}}`$ in $`R_2^C`$, and some refereed lower bounds of level 3 are withdrawn (the last table). **Later (the forty-fourth round):** the claim goes on to $`Z^{\mathrm{W}}`$ in $`R_2^C`$ and to $`[0, Z^{\mathrm{FP}})`$ in $`R_2^S`$, and the blocking point of the forty-third round toward $`\nu_3`$ is closed (the last table). **Later (the forty-fifth round):** the claim goes on to $`Z^{\mathrm{WW}}`$ in $`R_2^C`$ and to $`[0, Z^{\mathrm{W}})`$ in $`R_2^S`$ (the table of that round). **Later (the forty-sixth round):** the claim goes on to $`Z^{\mathrm{V}}`$ in $`R_2^C`$ and to $`[0, Z^{\mathrm{WW}})`$ in $`R_2^S`$, and the blocking point B-1 of the forty-fifth round is closed (the last table).

| node | statement | where | status | reviews | rests on |
|---|---|---|---|---|---|
| T0 | $`\nu_C = \nu_S = L(\omega+1)`$; the claim in $`R_2^C`$ on $`[0, \nu_C]`$ | [SHIFT7.md](SHIFT7.md) §2.1 | **not proved as written** (fortieth round) | 1 and the audit | T1, T2, T3, T4 |
| T1 | the lower half $`\nu_C \ge L(\omega+1)`$ | [SHIFT7.md](SHIFT7.md) §1.1 | **not proved as written** (fortieth round) | 1 | T1a–T1d |
| T1a | NU-LOW″: the $`\le_1`$-predecessors of $`x \ge L(\omega)`$ lie in $`[m^*, x)`$ | [SHIFT3.md](SHIFT3.md) §2.4 | proved under its conditions, given FRAG | 2 | T1b, T1c, S11 |
| T1b | CAP-0 below $`P'`$; LOW is false | [SHIFT7.md](SHIFT7.md) §1.1 | **not proved as written** (fortieth round) | 1 | S1 |
| T1c | CAP-1; the exact calculus at level 2 (link L2) | [SHIFT7.md](SHIFT7.md) §1.1 | **not proved as written** (fortieth round) | 2 (audit) | S1, S10 |
| T1d | LONG-CLASS$`^\omega`$ at level 2, LC-STRICT; MULTI-FAR$`_k`$ | [SHIFT7.md](SHIFT7.md) §1.1, §2.1; [SHIFT3.md](SHIFT3.md) §1 | LC-STRICT (inequalities) and MULTI-FAR$`_k`$ proved; LONG-CLASS$`^\omega`$ not proved as written | 1 (LC-STRICT 2) | S1, S3, T1c |
| T2 | the upper half $`\nu_C \le \nu_S \le L(\omega+1)`$ (PAIR, UP) | [SHIFT7.md](SHIFT7.md) §2.1 | **not proved as written** (fortieth round) | 2 (audit) | T2a–T2d |
| T2a | the shift criterion SHIFT | [SHIFT.md](SHIFT.md) §1 | proved | 1 (its hypotheses checked by the audit) | Wilken 2020, Prop. 21.11 |
| T2b | (C1), (C2), (P): $`L(n) \le_1 L(n+1)`$, $`L(n) \le_1 L(\omega) \le_1 L(\omega+1)`$ | [SHIFT7.md](SHIFT7.md) §2.1 | **not proved as written** (fortieth round) | 2 (audit) | T2b1 |
| T2b1 | CROSS-LIM: a restart with code and exponent $`\ge P'`$ reaches $`H(\eta + P')`$ (link L3) | [SHIFT7.md](SHIFT7.md) §2.1 | **not proved as written** (fortieth round): it crosses the code $`G_2 + P`$ | 2 (audit) | T2b2, T2b3, S2, S10 |
| T2b2 | LONG-RS$`^U`$, now LONG-RS$`^{\mathrm{rel}}`$: the long-restart step | [SHIFT2.md](SHIFT2.md) §1.1, §2.1; [SHIFT8.md](SHIFT8.md) §1.2 | proved, given FRAG, for every η-offset below $`\omega^c`$, $`c \lt \Omega_2`$, at every level (with CAP-SUPPLY, XA$`^p`$, FRAG2$`^{\mathrm{rel}}`$; written in the thirty-third round, R-1); CAP-SUPPLY (ii) not proved as written (fortieth round) | 1; the repaired form 2 | S13–S15 |
| T2b3 | realizers at every level | [SHIFT5.md](SHIFT5.md) §2.2; [SHIFT3.md](SHIFT3.md) §2.4 | proved | 1 / 2 | S11 |
| T2c | (C3): TC⁺$`^\omega`$, EMB, ONTO-FIN (link L3) | [SHIFT7.md](SHIFT7.md) §2.1 | **not proved as written** (fortieth round) | 2 (audit) | T2c1, T2c2, S1, S12 |
| T2c1 | THETA-EQ$`^{\mathrm{rel}}`$, EQUIV$`^{\mathrm{rel}}`$, EQ-F$`^{\mathrm{rel}}`$; for bases without a copy 2.6′ and TC⁺$`^{\mathrm{rel}}`$ (R-2) | [SHIFT7.md](SHIFT7.md) §1.1; [SHIFT8.md](SHIFT8.md) §1.2 | transfer | 1 | S3, S6 |
| T2c2 | the base changes BC$`^\pi`$ at every level; TC⁺ for short codes; READ-EQ | [SHIFT5.md](SHIFT5.md) §1.2, §2.2 | proved (TC⁺ given FRAG) | 1 | S11 |
| T2d | FIRST-PAIR, the cap CAP, NU-CT | [BREAK.md](BREAK.md) §2 | proved | 1 | S12 |
| T3 | the core half: $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$ | [BREAK.md](BREAK.md) §2 | proved | 1 | S12; Carlson 2009 |
| T4 | the names half: $`\nu_C \lt \psi_{\Omega_1}(I_\omega)`$, the normal form of $`L(\omega+1)`$ | [SHIFT.md](SHIFT.md) §1; [SHIFT7.md](SHIFT7.md) §2.5 | proved, checked (Lean); $`\nu_C \le L(\omega+1)`$ not proved as written | 1 | — |
| S1 | LAND$`^\omega`$: exact reaches and pins of every long code below $`P'`$ (FAR-PIN$`^{L,\mathrm{rel}}`$) | [SHIFT7.md](SHIFT7.md) §1.1 | **not proved as written** (fortieth round): the formula is false at $`m_0 \ge \Omega_1`$ | 1 | S2, S6–S9 |
| S2 | the exact calculus: families, HULL-ARITH, the crossing, the lower bound | [SHIFT6.md](SHIFT6.md) §3 | the exact values: false as stated at the affected codes; **not proved as written** (fortieth round) | 1 | S3, S7, S8, T2b2 |
| S3 | THETA$`^\omega`$: the readings of all codes below $`P'`$ (link L1) | [SHIFT6.md](SHIFT6.md) §3 | transfer | 2 (audit) | S4, S11 |
| S4 | PSI-θ$`^k`$, PSI-W$`^{(k)}`$, PSI-W (link L1) | [SHIFT6.md](SHIFT6.md) §3.2 | transfer; checked (order only) | 2 (audit) | S5 |
| S5 | PSI-n, CNST$`^n`$, PSI-θ | [SHIFT3.md](SHIFT3.md) §2.1 | proved | 1 | — |
| S6 | the closed points $`\mathrm{cl}_\nu`$: MONO-cl, AGREE, EQ-cl | [SHIFT6.md](SHIFT6.md) §3.1 | proved | 1 | S7 |
| S7 | EXACT-CL\*, GAP$`_j`$, ENUM | [SHIFT4.md](SHIFT4.md) §2.1 | proved, given FRAG | 1 | S13–S15 |
| S8 | FAR-PIN$`^L`$, MULTI-RC$`^L`$, TOP-REG-LAND; the moved-lower pin, SIM; FAR-PIN$`^{L4}`$ | [SHIFT5.md](SHIFT5.md) §1.1; [SHIFT6.md](SHIFT6.md) §1.2, §2.2 | transfer, given FRAG | 1 | S9, S13–S15 |
| S9 | the transport $`T^U`$, FAR-PIN$`^U`$, MULTI-RC$`^U`$ | [SHIFT2.md](SHIFT2.md) §2.1 | proved, given FRAG | 1 | S14 |
| S10 | the tools at every level, TAIL-LEVEL, OFF-INF at every level | [SHIFT5.md](SHIFT5.md) §2.2 | transfer (sample rows checked) | 1 | S11 |
| S11 | GEN-ALL; D-UNC at every level; SPLIT, DICT, EXT-ETA | [SHIFT5.md](SHIFT5.md) §1.3, §2.2; [SHIFT3.md](SHIFT3.md) §2.4 | proved (EXT-ETA by transfer) | 1 / 1 / 2 | — |
| S12 | SKEL⁺ below $`\nu_S`$ | [BREAK.md](BREAK.md) §2; [COVER.md](COVER.md) §5.1 | proved | 1 (R-3) | — |
| S13 | Theorem FRAG | [RESTARTS.md](RESTARTS.md) §1 | proved; also Lean ([LEAN.md](LEAN.md)) | 2 (audit) | [W07a], [W07b], S16 |
| S14 | FRAG-SUBST; SUBST-ISO, SUBST-COMM | [BREAK.md](BREAK.md) §4 | proved | 2 (audit); 1 | S13; [W07a] |
| S15 | Theorem FRAG2 | [RESTARTS.md](RESTARTS.md) §2 | proved; also Lean ([LEAN.md](LEAN.md)) | 2 (audit) | S13, S12 |
| S16 | the own proof of [W07b] L.2.1 and Thm 2.2 (in place of Wilken, AML 45) | an early round | proved | 1 | — |

Cited, each checked by the audit against the paper text: [W07a] Def 3.26–3.28, L.3.27, L.3.30, L.4.3, Def 5.1, L.5.3, L.5.5–5.7, Cor 5.4, Def 6.1, Def 6.2, L.6.3, L.6.9, L.6.10; [W07b] L.4.3,
L.4.4, Thm 5.3, Cor 5.7, Cor 5.9, Cor 5.10; Wilken 2020, Prop. 21.6, L.21.7, Prop. 21.11; Carlson 2009, L.5.5, L.5.7, Thm 14.10. Here [W07a] is Wilken, "Ordinal arithmetic based on Skolem
hulling", APAL 145 (2007) 130–161, and [W07b] is Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

Counts: 34 nodes; 11 are proved by transfer (T1c, T2b, T2b1, T2c, T2c1, S2, S3, S4, S8, S10, and EXT-ETA in S11).

**The three weakest links** (chosen by how much fails with them and how little they were checked): L1 = S3, S4; L2 = T1c with S10; L3 = T2, T2b, T2b1, T2c. The audit found no fatal
and no blocking point in them. Its minor points, and those of its referee, are in [SHIFT7.md](SHIFT7.md) §3.1. The one lemma that the chain uses but that is not written as a lemma is
LONG-RS$`^U`$ for η-offsets in $`[\psi_{\Omega_2}(\Omega_2), P')`$ (R-1): all its ingredients exist, and it is used at level 1 (by S1, S2, T1b, so by the lower half) and at level 2 (by T2b1).
It is now written (row T2b2).

**The residue, closed in the thirty-third round** ([SHIFT8.md](SHIFT8.md) §1.2; 1 review each, no fatal or blocking point):

- R-1: LONG-RS$`^{\mathrm{rel}}`$ with CAP-SUPPLY, proved given FRAG, after two one-line repairs of the referee (the bound of XA$`^p`$ must exceed $`\mathrm{lh}(x)`$ for the fixed points that are not
  restarts; for a $`\pi`$-coded restart take $`c = D' + 1`$).
- R-2 and L3-b: the identities of the calculus for bases without a copy (2.6′) and TC⁺$`^{\mathrm{rel}}`$, proved by transfer; the citations are corrected.
- L2-a, L1-b, L2-b: the audit rows at level 2, proved by transfer (the referee checked a sample of the rows).
- L1-a: CNST$`_j`$ past $`\theta`$ with countable constants, checked (0 failures; the referee confirmed it with a new seed). R-3 was corrected in the table already.
- In the thirty-fourth round every use of the long-restart step cites LONG-RS$`^{\mathrm{rel}}`$ with these two repairs, also at a base point that is not a bare cap, and its referee
  checked the instances ([SHIFT8.md](SHIFT8.md) §2.1; 2 reviews).
- Left: the crossing at $`m^*`$ across two levels has no audit row (not used by the milestone).

**The table of the fortieth round** ([SHIFT10.md](SHIFT10.md) §3.2; the second audit, with the corrections of its referee and of the referee of §3.1 there):

| result | status after the fortieth round |
|---|---|
| $`X_9`$, $`X_{11}`$, $`X_{12}`$, $`X_{13}`$, $`X_{14}`$ | stand (no exact long value at an affected code) |
| $`X_{15}`$ to $`X_{18}`$ | stand (exponents below $`G_2`$) |
| $`X_{19}^\flat`$, $`X_{19}^{\mathrm{lin}}`$ | proved (new; $`X_{19}^{\mathrm{lin}}`$ 2 reviews with §3.1 there) |
| $`X_{19}`$, $`X_{20}`$, $`X_{21}`$ | proved again with the corrected atoms (§3.1 there; 1 review of the repair) |
| $`X_{22}`$, $`X_{23}`$ | not proved as written |
| CAP-0 below $`P'`$, not-LOW, CAP-1, LONG-CLASS$`^\omega`$, NU-LOW″⁺, $`\nu_C \ge L(\omega+1)`$ | not proved as written |
| CROSS-LIM, (C1)–(C3), TC⁺$`^\omega`$, EMB, ONTO-FIN, PAIR, UP, NU, NU-NAME, LOW$`^\infty`$, $`\nu_C = \nu_S = L(\omega+1)`$, the claim on $`[0, \nu_C]`$ | not proved as written |
| LC-STRICT (the code inequalities), the criterion SHIFT, the core half $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$, the transport lemmas | stand |
| the frontiers above $`\nu_C`$ up to $`Z^\Lambda`$ ([SHIFT7.md](SHIFT7.md) §3.2 to [SHIFT10.md](SHIFT10.md) §1), and $`[0, Z^\varepsilon)`$ in $`R_2^S`$ | not proved as written |
| the exact long formulas at $`m_0 \ge \Omega_1`$, and the landing for $`2 \le D \lt \hat G`$ | false as stated (the upper bounds stand) |
| the lower-bound step (b) of [SHIFT2.md](SHIFT2.md) §3.1, the step (b) of NO-READL ([SHIFT5.md](SHIFT5.md) §2.1) | wrong as proved; no later theorem needs them |

**The table of the forty-first round** ([SHIFT11.md](SHIFT11.md) §1.1, §1.2; each result 1 review unless a count is given):

| result | status after the forty-first round |
|---|---|
| ENUM-REACH: $`r(\lambda) = k_\lambda(\Theta_\lambda(m))`$ for every code $`m \lt P'`$, levels 1 and 2 (replaces S1, S2) | proved, given FRAG |
| COUNT♯, LAND$`^{\omega\sharp}`$, NEST, SHADOW-PREFIX, BOUND♯, CAP♯, CROSS♯, MONO♯ | proved (the count without FRAG) |
| TRANSLATION$`^{(3)}`$ (every code below $`G(\hat\zeta_3)`$) | proved by transfer, given FRAG |
| CAP-0 below $`P'`$, not-LOW, CAP-1, LONG-CLASS$`^\Omega`$, NU-LOW″⁺, $`\nu_C \ge L(\omega+1)`$ (T1, T1b, T1c) | proved by transfer, given FRAG |
| CROSS-LIM, (H4) and CAP-SUPPLY at the crossed codes, (C1)–(C3), TC⁺$`^\omega`$ (with (EQ) for the maps that raise codes proved after ENUM-REACH), EMB, ONTO-FIN, PAIR, UP, NU (T2, T2b, T2b1, T2c) | proved by transfer, given FRAG |
| T0: $`\nu_C = \nu_S = L(\omega+1)`$, the claim on $`[0, \nu_C]`$; NU-NAME, LOW$`^\infty`$ | proved, given FRAG |
| $`X_{22}`$, $`X_{23}`$ | below $`\nu_C`$, so covered by T0 |
| $`X_9`$ to $`X_{18}`$, $`X_{19}^\flat`$, $`X_{19}^{\mathrm{lin}}`$; $`X_{19}`$ to $`X_{21}`$ | stand as written; with FAR-PIN$`^{L\sharp}`$ and EXP-BOUND (read again by the audit) |
| LB-b-FALSE, NO-CROSS$`^F`$, TRANSLATION$`^e`$, TC⁺♯, EXP-BOUND | proved (EXP-BOUND: the normal form of $`\hat\zeta_H`$ is checked) |
| EXACT-LONG$`^e`$ ([SHIFT6.md](SHIFT6.md) §1.2) | false at every code of its range |
| NO-READL ([SHIFT5.md](SHIFT5.md) §2.1) | not proved as written |
| the frontiers above $`\nu_C`$ up to $`Z^\Lambda`$, and $`[0, Z^\varepsilon)`$ in $`R_2^S`$ | not proved as written (the gap calculus is not run again) |


**The table of the forty-second round** ([SHIFT11.md](SHIFT11.md) §2.1, §2.2; each result 1 review):

| result | status after the forty-second round |
|---|---|
| EQ$`^{\mathrm{all}}`$: the corrected value commutes with every base change of the class BC$`^\pi`$, also those that raise constants (closes point m1 of the review of ENUM-REACH; T2c now cites it) | proved, given FRAG |
| T0: $`\nu_C = \nu_S = L(\omega+1)`$, the claim on $`[0, \nu_C]`$ | proved, given FRAG (the chain complete as written) |
| VAL-IF: above $`\nu_C`$ a reach of level 1 or 2 enters only through V0–V4 | proved, by reading |
| GAP-CALC$`^{\sharp\mathrm{reg}}`$ with the region condition (REG♯) | proved by transfer, given FRAG |
| FAR-PIN″♯, CROSS-LIM″♯, PAIR$`_j`$♯, LOW$`_j`$♯, C-TRANSFER♯, TC⁺″♯, TRANS-K″♯ | proved by transfer, given FRAG |
| Theorem C$`^{\Lambda\sharp}`$; the claim in $`R_2^C`$ on $`[0, Z^\Lambda]`$, $`\beta_0 \gt Z^\Lambda`$, and the frontiers $`X_A`$ to $`Z^\varepsilon`$ as restrictions | proved by transfer, given FRAG |
| $`r(b) = k''_b(o_b(c''))`$ at the restarts $`b = L(\lambda'')`$ below $`Z^\Lambda`$ | proved |
| $`Z^{\mathrm{LL}}`$ (Theorem C$`^{\mathrm{LL}}`$) | not proved (FALSE-LB″ is a conjecture) |
| $`\beta_0 \gt \nu_C`$; the claim in $`R_2^S`$ on $`[0, \nu_C]`$ and on $`[0, F_\nu)`$ | proved, given FRAG and EQ$`^{\mathrm{all}}`$ (the review's blocking point B-1 was this label) |
| Theorem X-COF, Lemma E1$`^p`$ | proved, without FRAG (for an admissible base) |
| UNIFORM-B, FIN-CROSS, K2$`^{\mathrm{cap}}`$ | proved, given their hypotheses (K2$`^{\mathrm{cap}}`$ after the repair m1) |
| $`R_2^S`$ on $`[0, Z^\varepsilon)`$ along the re-run | an outline |
| $`R_2^S`$ on $`[0, Z^\Lambda)`$; $`R_2^C`$ on $`[0, Q^\Lambda]`$ | conditional (labels checked only) |

**The table of the forty-third round** ([SHIFT11.md](SHIFT11.md) §3.1, §3.2; each result 1 review unless a count is given):

| result | status after the forty-third round |
|---|---|
| READ$`^{\mathrm{FP}}`$, RANGE″ (no long restart of level 3 is crossed below $`Z^{\mathrm{FP}}`$); NEST″, COUNT♯″, LAND″♯, SHADOW-PREFIX″ | proved, without FRAG |
| ENUM-REACH″$`^{\mathrm{FP}}`$: $`r(b) = k''_b(o_b(c''))`$ at every restart $`b = L(\lambda'')`$ below $`Z^{\mathrm{FP}}`$, long codes included (closes F-1 of [SHIFT10.md](SHIFT10.md) §2.1) | proved by transfer, given FRAG (with the review's m1) |
| EQ″ | proved for the far transport; for the other maps not proved as written (not used) |
| FALSE-LB″ | proved, given FRAG |
| LB″, EXACT-LONG-CL″\* ([SHIFT10.md](SHIFT10.md) §1.1); LB″$`^G`$, the strong CROSS″, CROSS-O″, EXACT-LONG″$`^G`$, EXACT-F″, the value of AGREE″ (§2.1 there) | false where the corrected value differs; withdrawn |
| Theorems C$`^{\mathrm{LL}\sharp}`$, C$`^{\mathrm{FP}\sharp}`$; the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{FP}}]`$, $`\beta_0 \gt Z^{\mathrm{FP}}`$; $`Z^{\mathrm{LL}}`$, $`L(\theta'_2\cdot\Omega_1)`$, $`L(\theta'_2\cdot\Omega_2)`$ as restrictions | proved by transfer, given FRAG |
| Theorem Z$`^{\mathrm{LG}}`$: $`\beta_0 \gt Z^{\mathrm{LG}}`$ and the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{LG}}]`$ with caps only (SKEL″$`^{\mathrm{cr}}`$, UPPER$`^{\mathrm{cr}}`$, PRED1$`^{\mathrm{cr}}`$, C$`^{\Lambda 1}`$) | proved by transfer, given FRAG; with §3.1, 2 reviews for $`(Z^\Lambda, Z^{\mathrm{LG}}]`$ |
| the claim in $`R_2^S`$ on $`[0, Z^\Lambda)`$; BLOCK″$`_0(Z^\Lambda)`$♯, $`\beta_0 \gt Q^\Lambda`$ | proved, given FRAG (was conditional) |
| UNIFORM-B⁺, K2$`^{\mathrm{cap}}`$ repaired | proved, given their hypotheses |
| S-COND | proved as an implication; the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{LG}})`$ conditional on LONG″-CAP |
| CAP-0″ below $`Z^{\mathrm{FP}}`$ (sharp form) | proved, given FRAG |
| LOW-RED″, BASE″, NU-LOW‴, SHIFT$`_3'`$ ($`L_3(\omega) \lt_2 L_3(\omega+1)`$) | proved as implications |
| $`T_3^S \le \nu_3`$, $`T_3^S = \nu_3`$ | not proved (blocking point B-1 of the review) |
| $`R_2^S`$ at $`Z^{\mathrm{FP}}`$; NU-CT$`_3`$ | outlines |

**The table of the forty-fourth round** ([SHIFT12.md](SHIFT12.md) §1.1, §1.2; each result 1 review unless a count is given):

| result | status after the forty-fourth round |
|---|---|
| TIER, THETA″$`^W`$ (the tiers $`G''(\Omega_2+x)`$, $`x \lt \omega^2`$, read in the window of the restart); the range lemmas up to $`Z^{\mathrm{W}}`$ (no long restart of level 3 is crossed) | proved, without FRAG |
| ENUM-REACH″$`^{\mathrm{W}}`$: $`r(b) = k''_b(o_b(c''))`$ at every restart $`b = L(\lambda'')`$ below $`Z^{\mathrm{W}}`$; codes $`\ge \hat G''`$ land at $`F''_b`$ | proved by transfer, given FRAG |
| Theorem C$`^{\mathrm{W}\sharp}`$; the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{W}}]`$, $`\beta_0 \gt Z^{\mathrm{W}}`$; the points $`L(\theta'_2\cdot(\Omega_2+x))`$ as restrictions | proved by transfer, given FRAG |
| CAP-0″ below $`Z^{\mathrm{W}}`$ (sharp form); the far top lemma with the larger set of pins (m1 of the forty-third review) | proved, given FRAG |
| TAUL | proved, without FRAG |
| SKEL″$`^\nu`$ (the skeleton of a region of level 3 below $`y_3`$ with any $`\le_1`$-predecessors) | proved by transfer, given FRAG, below $`\min(y_3, L(\Omega_\omega))`$; above it an implication |
| SHIFT$`_3''`$: from (Y), (H2$`^{\mathrm{cr}}`$), (H3), $`L_3(\omega) \lt_2 \nu_3`$ with a triple nest, $`T_3^S = y_3 = \nu_3`$ (closes B-1 of the forty-third round) | proved as an implication, given FRAG |
| NU-LOW‴ with the hypotheses of the forty-third review | proved as an implication |
| $`\nu_3`$; CAP-0″ on $`[Z^{\mathrm{W}}, L(\Omega_\omega))`$, CAP-1″, LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$), LEFT⁺ one level up | open |
| (H3), NU-CT$`_3`$; the second window; $`R_2^S`$ at $`Z^{\mathrm{W}}`$ | outlines |
| the first crossing of a long restart of level 3 at the code $`G''(\theta'_3\cdot\omega^2)`$ | conjecture |
| $`r(Z^\Lambda) = \delta''_1(L(\theta'_2\cdot\omega^2+\omega^2)) + 1`$; LONG″-CAP (the conjecture of the forty-third round) | proved, given FRAG |
| LOC-PASS | proved |
| S-PAST-Λ: the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{LG}})`$ | proved, given FRAG |
| S-FOLLOW; the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{FP}})`$ and Carlson's criterion below $`Z^{\mathrm{FP}}`$ | proved, given FRAG |
| the induction with caps only at the base $`Z^{\mathrm{FP}}`$: $`\beta_0 \gt Z^{\mathrm{FPG}}`$, the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{FPG}}]`$ | proved by transfer, given FRAG; with the row of C$`^{\mathrm{W}\sharp}`$, 2 reviews for $`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$ |
| S-COND$`^{\mathrm{FP}}`$ | proved as an implication |
| the remark "$`Z^{\mathrm{FP}}`$ is in the core of $`R_2^S`$ if and only if an indecomposable $`\mu`$ lies in $`(r(Z^{\mathrm{FP}}), \beta_0]`$" | only the "if" half is proved |
| CAP$`^{\mathrm{FP}}`$ (a cap on $`r(Z^{\mathrm{FP}})`$) | conjecture |

**The table of the forty-fifth round** ([SHIFT12.md](SHIFT12.md) §2.1, §2.2; each result 1 review unless a count is given; $`\lambda_{\mathrm{FP}}`$ and $`\lambda_{\mathrm{W}}`$ are the indices of $`Z^{\mathrm{FP}}`$ and $`Z^{\mathrm{W}}`$):

| result | status after the forty-fifth round |
|---|---|
| the tiers $`G''(\Omega_2+x)`$ for $`x \lt G''(\Omega_2\cdot 2)`$, read in the second window $`[F''_b, L(\lambda''+\Omega_1\cdot 2))`$; no index of $`L`$ in $`[\theta'_2\cdot(\Omega_2+G''(\Omega_2\cdot 2)), \theta'_2\cdot\Omega_2\cdot 2)`$ | proved, without FRAG |
| the far pins on the second window (transport, pins, top lemma, long restart step, crossing lemma) | proved by transfer, given FRAG |
| ENUM-REACH″$`^{\mathrm{W2}}`$: $`r(b) = k''_b(o_b(c''))`$ at every restart below $`Z^{\mathrm{W2}}`$; every restart crossed is short; $`r(Z^{\mathrm{W}}) = \delta''_1(L(\theta'_2\cdot(\Omega_2+\omega^2)+\Omega_1+\omega^2)) + 1`$ | proved by transfer, given FRAG |
| Theorem C$`^{\mathrm{W2}\sharp}`$; the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{W2}}]`$, $`\beta_0 \gt Z^{\mathrm{W2}}`$ | proved by transfer, given FRAG |
| the readings $`o_b(G''(\Omega_2\cdot\xi+x)) = L(\lambda''+\Omega_1\cdot o_b(\xi)+o_b(x))`$ below $`\Omega_2^2`$; the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{WW}}]`$, $`\beta_0 \gt Z^{\mathrm{WW}}`$ | proved by transfer, given FRAG (the review checked the weakest steps) |
| CAP-0″ below $`Z^{\mathrm{WW}}`$ (sharp form) | proved, given FRAG |
| the first crossing of a long restart of level 3 at the code $`G''(\theta'_3\cdot\omega^2)`$ | conjecture |
| CAP$`^{\mathrm{FP}}`$: $`r(Z^{\mathrm{FP}})`$ and the reaches of $`L(\lambda_{\mathrm{FP}} + G''(\omega^2)\cdot k)`$ | proved, given FRAG |
| S-F2: the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{W}})`$, Carlson's criterion below $`Z^{\mathrm{W}}`$ | proved, given FRAG |
| S-FPG: the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{FPG}})`$ by caps | proved, given FRAG; with S-F2, 2 reviews for $`[0, Z^{\mathrm{FPG}})`$ |
| BASE-TEST″ and the table of base points in $`(Z^{\mathrm{FP}}, Z^{\mathrm{W}}]`$ | proved, except the row of $`Z^{\mathrm{W}}`$ |
| the induction with caps only at the base $`Z^{\mathrm{W}}`$: $`\beta_0 \gt Z^{\mathrm{WG}}`$, the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{WG}}]`$ | proved by transfer, given FRAG; with ENUM-REACH″$`^{\mathrm{W2}}`$, 2 reviews for $`(Z^{\mathrm{W}}, Z^{\mathrm{WG}}]`$ |
| S-COND$`^{\mathrm{W}}`$ | proved as an implication |
| LB$`^{\mathrm{W}}`$ as proved in the $`R_2^S`$ paper | not proved (blocking point B-1); the value of $`r(Z^{\mathrm{W}})`$ comes from ENUM-REACH″$`^{\mathrm{W2}}`$ |
| the claim in $`R_2^S`$ on $`[0, L(\lambda_{\mathrm{W}} + G''(\omega^2)))`$ from $`r(Z^{\mathrm{W}})`$ and S-COND$`^{\mathrm{W}}`$ | not refereed as a combination; not counted |
| CAP$`^{\mathrm{W}}`$ (ii) | conjecture |
| $`\nu_3`$; LEFT⁺ one level up, CAP-1″, LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$) | open |

**Later (the forty-sixth round):** LB$`^{\mathrm{W}}`$ and CAP$`^{\mathrm{W}}`$ (ii) are proved, and the combination above is replaced by a refereed proof (next table).

**The table of the forty-sixth round** ([SHIFT12.md](SHIFT12.md) §3.1, §3.2; each result 1 review unless a count is given; a multiplier is a $`\zeta \lt \psi_{\Omega_3}(0)`$):

| result | status after the forty-sixth round |
|---|---|
| the step $`(Z^{\mathrm{W2}}, Z^{\mathrm{WW}}]`$ written out in full (the domain of $`L`$ at $`\lambda''+\Omega_1\cdot u`$, the readings below $`\Omega_2^2`$, the link of code $`\Omega_1+c`$) | proved, without FRAG (the link given FRAG); read in full in this round, at its weakest steps in the forty-fifth |
| THETA″$`^{\mathrm{V}}`$: the tier lemma and the reading $`o_b(G''(\zeta)) = L(\lambda''+1+R''_b(\zeta))`$ for every normal multiplier | proved, without FRAG |
| the links of code $`\Omega_1\cdot m+d`$ (sums only) and of every Veblen code up to $`\psi_{\Omega_2}(0)`$ | proved; the second given FRAG |
| the far pins with threshold $`\psi_{\Omega_2}(0)`$; ENUM-REACH″$`^{\mathrm{V}}`$ below $`Z^{\mathrm{V}}`$ | proved by transfer, given FRAG |
| Theorem C$`^{\mathrm{V}\sharp}`$; the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{V}}]`$, $`\beta_0 \gt Z^{\mathrm{V}}`$ | proved by transfer, given FRAG; $`(Z^{\mathrm{WW}}, L(\theta'_2\cdot\Omega_2^\omega)]`$ uses the links by sums only |
| CAP-0″ below $`Z^{\mathrm{V}}`$ (sharp form); no long restart crossed below $`Z^{\mathrm{V}}`$; $`r(Z^{\mathrm{V}})`$ | proved, given FRAG |
| the multipliers with $`\psi_{\Omega_3}`$-atoms | open |
| the claim up to $`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_3))`$; the first crossing of a long restart of level 3 at the code $`G''(\theta'_3\cdot\omega^2)`$ | conjecture |
| CAP$`^{\mathrm{W}}`$ and LB$`^{\mathrm{W}}`$ (closes B-1) | proved, given FRAG |
| the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{WG}})`$, $`[0, Z^{\mathrm{W2}})`$ and $`[0, Z^{\mathrm{WW}})`$; Carlson's criterion below $`Z^{\mathrm{WW}}`$ | proved, given FRAG; with S-F2, 2 reviews for $`[0, Z^{\mathrm{W}})`$ |
| BASE-TEST″ and the table of base points in $`(Z^{\mathrm{W}}, Z^{\mathrm{WW}}]`$ | proved |
| the induction with caps only at the bases $`Z^{\mathrm{W2}}`$ and $`Z^{\mathrm{WW}}`$: $`\beta_0 \gt Z^{\mathrm{WWG}}`$, the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{WWG}}]`$ | proved by transfer, given FRAG; with C$`^{\mathrm{V}\sharp}`$, 2 reviews for $`(Z^{\mathrm{WW}}, Z^{\mathrm{WWG}}]`$ |
| CAP$`^{\mathrm{W2}}`$: $`r(Z^{\mathrm{W2}})`$ | proved, given FRAG |
| CAP$`^{\mathrm{WW}}`$; the claim in $`R_2^S`$ past $`Z^{\mathrm{WW}}`$ from it | conjecture (its value (i) is a row of ENUM-REACH″$`^{\mathrm{V}}`$); the combination is not refereed, not counted |
| $`\nu_3`$; LEFT⁺ one level up, CAP-1″, LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$) | open |

**Later (the forty-seventh round):** the row $`r(Z^{\mathrm{V}})`$ above is conditional as proved there (its proof reads a reach above $`Z^{\mathrm{V}}`$, outside the range of the induction; B-1 of
the review of [SHIFT13.md](SHIFT13.md) §1.2); the value is proved again by ENUM-REACH″$`^\theta`$. CAP$`^{\mathrm{WW}}`$ is proved (next table).

**The table of the forty-seventh round** ([SHIFT13.md](SHIFT13.md) §1.1, §1.2; each result 1 review unless a count is given; a multiplier is a $`\zeta \lt \theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$, and
$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$):

| result | status after the forty-seventh round |
|---|---|
| DOWN″, CMAX and the criterion for the domain of $`L`$ at every index (m1 of the review of the forty-sixth round) | proved, without FRAG |
| THETA″$`^\theta`$: the tier lemma and the reading $`o_b(G''(\zeta)) = L(\lambda''+1+R''_b(\zeta))`$ for every normal multiplier, onto the offsets below $`\theta`$ | proved, without FRAG |
| EXACT-GS⁺ | proved, without FRAG |
| the links of every code below $`\theta`$; the far pins with threshold $`\theta`$ (below the endpoint $`L(\lambda''+\theta)`$) | proved, given FRAG |
| ENUM-REACH″$`^\theta`$ below $`Z^\theta`$, with $`r(Z^{\mathrm{V}})`$ and $`r(Z^\Phi)`$ | proved by transfer, given FRAG |
| Theorem C$`^{\theta\sharp}`$; the claim in $`R_2^C`$ on $`[0, Z^\theta]`$, $`\beta_0 \gt Z^\theta`$, $`T_3^C \gt Z^\theta`$ | proved by transfer, given FRAG; $`(Z^{\mathrm{V}}, Z^\Phi]`$ uses only the tier of the $`\Gamma`$-atoms, $`(Z^\Phi, Z^{\mathrm{E}}]`$ also EXACT-GS⁺ |
| CAP-0″ below $`Z^\theta`$ (sharp form); no long restart crossed below $`Z^\theta`$ | proved, given FRAG |
| PLATEAU″-3, ALIGN″, HN″, MONO″ (without constants); LONG-FIRST″ as an implication | proved |
| THETA″$`^{\mathrm{READ}}`$; the claim up to $`L(\theta'_2\cdot\theta'_2)`$ | conjecture |
| the pins at links of codes in $`[\theta, P')`$; $`r(Z^\theta)`$ | open |
| CAP$`^{\mathrm{WW}}`$: $`r(Z^{\mathrm{WW}})`$, $`r(Z^{\mathrm{WWG}})`$ and the restarts between | proved, given FRAG |
| the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{WWG}})`$, $`[0, L(\theta'_2\cdot\Omega_2^\omega))`$ and $`[0, Z^{\mathrm{V}})`$; Carlson's criterion below $`Z^{\mathrm{V}}`$ | proved, given FRAG; 2 reviews for $`[0, Z^{\mathrm{WW}})`$ |
| BASE-TEST″$`^{\mathrm{V}}`$, NEXT-BASE″$`^{\mathrm{V}}`$ and the table of base points in $`(Z^{\mathrm{WW}}, Z^{\mathrm{V}})`$ | proved |
| the induction with caps only at the base $`Z^{\mathrm{V}}`$: $`\beta_0 \gt Z^{\mathrm{VG}}`$, the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{VG}}]`$ | proved by transfer, given FRAG; with C$`^{\theta\sharp}`$, 2 reviews for $`(Z^{\mathrm{V}}, Z^{\mathrm{VG}}]`$ |
| the claim in $`R_2^S`$ on $`[0, L(\lambda_{\mathrm{V}}+G''(\omega^2)))`$, $`Z^{\mathrm{V}} \in \mathrm{Core}(R_2^S)`$ | not proved (blocking point B-1: it used $`r(Z^{\mathrm{V}})`$ from outside the range of an induction); with ENUM-REACH″$`^\theta`$ the combination is not refereed, not counted |
| CAP$`^{\mathrm{V}}`$ (ii) | conjecture |
| $`\nu_3`$; LEFT⁺ one level up, CAP-1″, LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$) | open |

**Later (the forty-eighth round):** in the table above, the row on $`R_2^S`$ past $`Z^{\mathrm{V}}`$ (blocking point B-1) is closed: CAP$`^{\mathrm{V}}`$ is proved as an instance of ENUM-REACH″$`^\theta`$,
whose induction covers the window of $`Z^{\mathrm{V}}`$; $`r(Z^\theta)`$ and the links of codes in $`[\theta, P')`$ are proved (next table).

**The table of the forty-eighth round** ([SHIFT13.md](SHIFT13.md) §2.1, §2.2; each result 1 review unless a count is given; $`\Phi^{P'} = \psi_{\Omega_2}(\Omega_\omega\cdot 2+\Omega_2)`$):

| result | status after the forty-eighth round |
|---|---|
| SHIFT$`^K`$ (the shift of the levels with constants); the argument bounds; the domain of $`L`$ for offsets below $`\Phi^{P'}`$ at every base; the empty plateau $`[\zeta^*, \Omega_3)`$, $`\zeta^* = \psi_{\Omega_3}(\Omega_\omega\cdot 2+\Omega_3)`$ | proved, without FRAG |
| THETA″$`^{\Omega_3}`$: the reading of every normal multiplier below $`\Omega_3`$ onto the offsets below $`\Phi^{P'}`$ | proved, without FRAG |
| the links of every code in $`[\theta, P')`$ (the relative far pin one level up), the endpoint $`\theta`$ of the forty-seventh round included | proved by transfer, given FRAG |
| the links of every code in $`[P', \Phi^{P'})`$ (L-PIN and H-RC at an arbitrary image) | proved by transfer, given FRAG |
| ENUM-REACH″$`^{\Omega_3}`$ below $`Z^{\Omega_3}`$; $`r(Z^\theta)`$, $`r(N^\theta)`$, $`r(Z^{\theta'})`$ | proved by transfer, given FRAG |
| Theorem C$`^{\Omega_3\sharp}`$; the claim in $`R_2^C`$ on $`[0, Z^{\Omega_3}]`$, $`\beta_0 \gt Z^{\Omega_3}`$, $`T_3^C \gt Z^{\Omega_3}`$ | proved by transfer, given FRAG; $`[0, Z^{\theta'}]`$ without the links of codes in $`[P', \Phi^{P'})`$ |
| CAP-0″ below $`Z^{\Omega_3}`$; no long restart crossed below $`Z^{\Omega_3}`$ | proved, given FRAG |
| THETA″$`^{\mathrm{READ}}`$ on $`[\Omega_3, \theta'_3\cdot\omega^2]`$; the next frontier $`\psi_{\Omega_1}(\Omega_\omega\cdot 2+\omega^{\theta'_3+2})`$ | conjecture |
| the links of codes in $`[\Phi^{P'}, G''(\omega^2))`$ | open |
| CAP$`^{\mathrm{V}}`$: $`r(Z^{\mathrm{V}})`$, $`r(Z^{\mathrm{VG}})`$ and the restarts between (B-1 closed) | proved, given FRAG |
| the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{VG}})`$ with $`Z^{\mathrm{V}} \in \mathrm{Core}(R_2^S)`$, and on $`[0, Z^\theta)`$; Carlson's criterion below $`Z^\theta`$ | proved, given FRAG; 2 reviews for $`[0, Z^{\mathrm{V}})`$ |
| BASE-TEST″$`^\theta`$, NEXT-BASE″$`^\theta`$, FIRST-LL and the table of base points in $`(Z^{\mathrm{V}}, Z^\theta)`$ | proved |
| the induction with caps only at the base $`Z^\theta`$: $`\beta_0 \gt Z^{\theta\mathrm{G}}`$, the claim in $`R_2^C`$ on $`[0, Z^{\theta\mathrm{G}}]`$ | proved by transfer, given FRAG; with C$`^{\Omega_3\sharp}`$, 2 reviews for $`(Z^\theta, Z^{\theta\mathrm{G}}]`$ |
| S-COND$`^\theta`$ (the claim in $`R_2^S`$ past $`Z^\theta`$ from the reaches of its window) | proved as an implication; with $`r(Z^\theta)`$ the combination is not refereed, not counted |
| $`\nu_3`$; LEFT⁺ one level up, CAP-1″, LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$) | open |
