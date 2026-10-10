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

**Later (the forty-second round, [SHIFT11.md](SHIFT11.md) §2.1):** the step TC⁺$`^\omega`$ for $`B_n`$ (T2c) now cites EQ$`^{\mathrm{all}}`$, so T0 is complete as written; and the gap calculus above $`\nu_C`$ is run again, so the frontiers up to $`Z^\Lambda`$ are proved again (the table of the forty-second round at the end of this page).

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
