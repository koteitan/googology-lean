[← Back](README.md) | [English](SHIFT11.md) | [Japanese](SHIFT11-ja.md)

# $`R_2^+`$, the forty-first round: the exact long reach for every code below $`P'`$, the milestone $`\nu_C = \nu_S = L(\omega+1)`$ again, the audit up to $`X_{21}`$, and INC1 in Lean

This page continues [SHIFT10.md](SHIFT10.md) (§3 there is the fortieth round); §1 is the forty-first round. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a fatal or blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known, or of the target, is not counted as progress.

## 1. The forty-first round

Three papers (2026-10): the exact long reach for every code below $`P'`$ with the chain to $`\nu_C`$ run again (§1.1) and an audit of every exact long formula below $`X_{21}`$ (§1.2), each refereed
once, and the second Lean stage for $`R_2^C`$ (§1.3), whose audit checked the axioms and the definitions (Lean checks the proofs). A result in this section has 1 review unless a count is given.

**The milestone is proved again.** Given FRAG,

```math
\nu_C = \nu_S = L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P'),\qquad P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2),
```

and **Wilken's claim holds in $`R_2^C`$ on $`[0, \nu_C]`$, both halves** (1 review of the new proof, §1.1). The first proof ([SHIFT7.md](SHIFT7.md) §2.1) used exact long reaches that are false for
some codes ([SHIFT10.md](SHIFT10.md) §3.2); the new proof uses the corrected value $`r(\lambda) = k_\lambda(\Theta_\lambda(m))`$, now proved for every code below $`P'`$. LOW is false again (given FRAG).
In $`R_2^S`$ the claim is still proved only up to $`\upsilon_{\omega^3}`$; what is new there is $`\nu_S = \nu_C`$ and the agreement of the two structures on every relation with right end below $`\nu`$.
Everything recorded above $`\nu_C`$ ([SHIFT7.md](SHIFT7.md) §3.2 to [SHIFT10.md](SHIFT10.md) §1) stays not proved as written: its exact calculus in the gaps is not yet run again.

Papers cited: in §1.1 and §1.2 only through refereed stages: [W07b] (L.2.1), Wilken's "A glimpse of Σ₃-elementarity" (Prop 21.6, L.21.7, Prop 21.11), Carlson 2009 (L.5.5, L.5.7,
Thm 14.14) and, in §1.2, [C11] (Cor 0.8). In §1.3: Carlson 2009 (L.4.4, L.4.5, L.5.5 (7), Thm 14.10, Thm 14.14), [W07a] (Def 9.1, Thm 3.23), [W07b] (L.2.1, Def 5.8, Cor 5.9, Cor 5.10,
Claim 5.6) and Wilken 2020 (Def 21.4, Prop 21.6). None uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006). Levels are numbered as in [SHIFT8.md](SHIFT8.md) (one higher than in
the papers). Notation of [SHIFT10.md](SHIFT10.md) §3; $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, a restart $`\lambda`$ has $`\rho_\lambda = H(\eta_\lambda)`$, and $`P = \theta = \psi_{\Omega_2}(\Omega_\omega)`$.

The minor points of the reviews of the fortieth round are applied in the papers of §1.1 (m1–m5 of the review of [SHIFT10.md](SHIFT10.md) §3.1; m4 there now has a direct proof that the new value
is at most the old one) and §1.2 (the points B-2 and B-3 of the review of §3.2 there). The blocking point B-1 of that review (LB-CORR needed the invariance of the corrected value) is closed:
the corrected value is now an explicit formula that the transports carry both ways (§1.1), so no step "the least closed point above" is left.

### 1.1 The exact long reach for every code below $`P'`$ (ENUM-REACH), and $`\nu_C = \nu_S = L(\omega+1)`$ again

- **Visible restarts and the count** (proved, without FRAG, given the reaches of the restarts below the landing). A restart $`\nu`$ above $`\lambda`$ is **shadowed** if some restart $`R`$ with
  $`\rho_\lambda \lt \rho_R \lt \rho_\nu`$ has $`r(R) \gt \rho_\nu`$, and **visible** otherwise. For a restart $`\nu`$ let $`N(\nu)`$ be the restart whose region contains $`r(\nu)`$ and $`\mathrm{kc}(\nu)`$ the short code with
  $`r(\nu) = F(N(\nu), \mathrm{kc}(\nu))`$ (for a short $`\nu`$: $`N(\nu) = \nu`$, $`\mathrm{kc}(\nu) = \tau_\nu`$). NEST: the reach intervals of restarts inside a reach interval are nested. COUNT♯: the visible restart
  points form a closed set, and $`K_\lambda \cap [\delta_\lambda, \rho_\nu)`$ has order type exactly $`\rho_\nu`$ for every visible $`\nu \ne \lambda`$. So, with $`\hat\nu`$ the last visible restart point $`\le p`$ and $`N = N(\hat\nu)`$:

```math
k_\lambda(p) = F\bigl(N, \Theta_N^{-1}(\Theta_N(\mathrm{kc}(\hat\nu)) + s)\bigr),\qquad s = -\rho_{\hat\nu} + p\qquad(\text{LAND}^{\omega\sharp}).
```

  No fragmentation lemma is needed. The referee recomputed every worked value of the paper by hand from this formula. Minor point m6: the rule for the next visible point must exclude $`\lambda`$
  itself (the next one after $`\lambda`$ is $`R_1`$).
- **SHADOW-PREFIX, BOUND♯, CAP♯, CROSS♯, MONO♯** (proved). A restart $`H(\eta_\lambda + z)`$ that shadows $`H(\eta_\lambda + \xi)`$ has $`z`$ a prefix of the Cantor normal form of $`\xi`$; so whether the
  landing is visible is decided by finitely many atoms at smaller codes, and these facts transport. The landing offset of a code $`m`$ is below $`\omega^m`$, and $`r(\lambda) \lt H(\eta_\lambda + \omega^{m_\lambda})`$ (CAP♯).
  Every code that these lemmas need is smaller than $`m`$, so the induction below is not circular.
- **Theorem TRANSLATION$`^{(3)}`$** (proved by transfer, given FRAG). Codes below $`G(\hat\zeta_3)`$ ($`\hat\zeta_3 = \theta_3\cdot\omega^2`$) cross no long restart: the landing $`\nu`$ is the last restart point
  $`\le \Theta_\lambda(m)`$, it is short, and $`r(\lambda) = F(\nu, \Theta_\nu^{-1}(\Theta_\nu(\tau_\nu) + s))`$ with $`s = -\rho_\nu + \Theta_\lambda(m)`$, uncountable offsets included. This extends TRANSLATION of
  [SHIFT10.md](SHIFT10.md) §3.1 from $`\hat G + G_2`$ to $`G(\hat\zeta_3)`$, and corrects it: the first long restart that a reach crosses is $`H(\eta_\lambda + G_2)`$ (code $`G_2`$), reached at the code
  $`G(\hat\zeta_3)`$, and the shift of the indices starts at its $`R_1`$. Minor point m7: the strict inequality must cite the strict form of MONO and LC-STRICT ([SHIFT7.md](SHIFT7.md) §1.1).
- **Theorem ENUM-REACH** (proved, given FRAG). For every code $`m \lt P'`$ at levels 1 and 2 (π-codes included):

```math
r(\lambda) = k_\lambda(\Theta_\lambda(m)),
```

  both halves. The proof is the induction of the relative far pin ([SHIFT7.md](SHIFT7.md) §1.1) on the code, with the new atom, and four clauses at each code $`m`$: (EQ) the value commutes with
  the transports and base changes, (MR) the pins with moved lower parameters at smaller codes, (EX) the value, (RP) the relative long pin with the new atom. "$`\ge`$" uses LONG-RS$`^{\mathrm{rel}}`$
  ([SHIFT8.md](SHIFT8.md) §1.2); "$`\le`$" uses the top pin TOP-REG-LAND ([SHIFT5.md](SHIFT5.md) §1.1) with the target $`y = F(N, \mathrm{kc}(\hat\nu) + x)`$; each half meets the exact hypotheses of
  the refereed lemma. The referee's minor points, to be applied before the record (done here): (EQ) must be split (m1): for the transports under which codes do not grow ($`T^U`$, $`T''_g`$) it
  is proved inside the induction; for the maps that move constants up (the base changes $`B_n`$, the pieces of FRAG″) an image code can be $`\ge m`$, so (EQ) for them is proved after the
  theorem, by induction on the source code, and TC⁺$`^\omega`$ below cites this second part; a tail can be absorbed, and then $`r(\mu) \lt H(\eta_\mu + \omega^{m_\mu}) \le T(y)`$ by CAP♯ (m2); the moved
  points of the target can lie in shadowed regions between $`\hat\nu`$ and the landing, and the pin MULTI-RC$`^L`$ of [SHIFT5.md](SHIFT5.md) §1.1 along the landing offset covers them (m3, with a witness at the
  code $`G(\hat\zeta_A) + G(\zeta')`$); for a short realizer code take $`c = 3`$ (m5).
- **Corrections** (proved). The old calculus of families and overshoots ([SHIFT6.md](SHIFT6.md) §3) is false where the corrected value is lower: the code $`G(\hat\zeta_A)`$ reaches
  $`\delta_{F'} + \rho_{F'}\cdot 2`$ with $`\rho_{F'} = H(\eta_\lambda + \hat G + \Omega_1)`$, below the old value, and $`G(\hat\zeta_3 + \omega^2)`$ reaches $`\delta_L + L`$ with $`L = H(\eta_\lambda + G_2 + \omega^2)`$.
- **The chain to $`\nu_C`$ again** (proved by transfer, given FRAG; this re-run has 1 review). Each step of [SHIFT7.md](SHIFT7.md) §1.1, §2.1 is run again with BOUND♯, CROSS♯ and (EQ) in place of the
  old calculus: CAP-0 below $`P'`$, **not-LOW** ($`\nu_C \gt m^* = \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$), CAP-1, LONG-CLASS$`^\Omega`$, NU-LOW″⁺ and $`\nu_C \ge L(\omega+1)`$ (the lower half); CROSS-LIM, now from
  $`r(\mu) \ge \Theta_\mu(c_k)`$; (H4) and CAP-SUPPLY at every crossed code, with the exact value at the code $`G_2 + P`$: $`r(\lambda) = \delta_{R_1} + \upsilon_{\lambda+1}`$, which commutes with the transports; then
  (C1)–(C3), TC⁺$`^\omega`$, EMB, ONTO-FIN, PAIR, UP and NU (the upper half). So $`\nu_C = \nu_S = L(\omega+1)`$, and with the core half ([BREAK.md](BREAK.md) §2) and the normal form of $`L(\omega+1)`$
  (Lemma L), Wilken's claim holds in $`R_2^C`$ on $`[0, \nu_C]`$. With it NU-NAME, an exact reach for every restart below $`\nu`$, no ghost pair in $`R_2^C`$, the agreement of $`R_2^S`$ and $`R_2^C`$ on
  every relation with right end below $`\nu`$, and LOW$`^\infty`$ (from UP). The frontiers between $`X_{21}`$ and $`\nu_C`$ ($`X_{22}`$, $`X_{23}`$) are superseded: CAP-0 below $`P'`$ covers them (a remark).
- **The weakest steps** (named by the author; the referee checked their hypotheses but did not re-derive the cited pins and copies line by line): the "$`\le`$" pin of the target, whose code
  carries a moved point; (EQ) on the test of visibility; TC⁺$`^\omega`$ for $`B_n`$.
- **Not run again** (open). Everything above $`\nu_C`$: the exact calculus in the gaps (the reaches of the points $`L(e)`$ and of the restarts with codes $`\ge P'`$, GAP-CALC$`^{\mathrm{reg}}`$), so the
  frontiers $`X_A`$ to $`Z^\Lambda`$ and $`[0, Z^\varepsilon)`$ in $`R_2^S`$ stay not proved as written; one level up (C$`^{\mathrm{LL}}`$, C$`^{\mathrm{FP}}`$) stays an outline. Of the hypothesis (H0) of
  [SHIFT10.md](SHIFT10.md) §3.1, only the gap calculus is missing.

### 1.2 The audit: every exact long formula below $`X_{21}`$, and the chain to $`X_{21}`$

- **The test** (proved, by reading). A step is affected only if it uses a realizer code with a constant $`\ge \rho_\lambda`$, or an exact long value at an affected code (as an atom of a far pin, as
  the cap of a crossed long restart, under a base change, or as a stated formula). Lower bounds whose realizer codes are read at the restart itself (RL-UP, RL-UNC, CROSS, RL-2, RL-U,
  CROSS-U, CROSS-SHARP, PLAT-SHARP, LB$`^\theta`$, and the short exact values) are not affected.
- **LB-b-FALSE** (proved, given FRAG). The lower-bound step (b) of [SHIFT2.md](SHIFT2.md) §3.1 is false, also with the restriction that the review of [SHIFT10.md](SHIFT10.md) §3.2 proposed (the
  reflected codes taken at the restart itself). Witness: a restart $`\lambda`$ of code $`G_2 + P`$ below $`X_6`$ and the code $`\Omega_1 + 1`$; the step claims $`r(\lambda) \ge \delta_{R_1} + R_1 + 1`$, but
  $`r(\lambda) = \delta_{R_1} + \upsilon_{\lambda+1}`$. The same witness refutes the lower ends of the brackets of [SHIFT2.md](SHIFT2.md) §3.1 and [SHIFT3.md](SHIFT3.md) §1.1, and the lower bounds of
  [SHIFT3.md](SHIFT3.md) §1.1 and §2.1. The referee: the hypothesis must be $`\rho_{\lambda+\omega^2\cdot 3} \le \nu_S`$, as in the cited source, and its own check shows that the witness satisfies it (m1); the
  header should say that the review's restriction was on the reflected codes (m5).
- **NO-CROSS$`^F`$** (proved by transfer, given FRAG). A restart $`\lambda`$ of code $`\hat G + G_2`$ reaches exactly $`\delta_F + \rho_F + R_1 \lt \rho_{F+\omega^2}`$, where $`F`$ is the restart at $`F_\lambda`$. So the crossing
  and EXACT-LONG$`^e`$ of [SHIFT6.md](SHIFT6.md) §1.2 are false (a witness below $`X_{21}`$); this clash is the one between the corrected and the old value at $`F`$, which [SHIFT10.md](SHIFT10.md) §3.1 settled.
- **TRANSLATION$`^e`$** (proved by transfer, given FRAG). Every code $`m \in [\hat G, \varepsilon_{\hat G+1})`$ lands at $`F`$: $`r(\lambda) = r(F) + (-F_\lambda + \Theta_\lambda(m))`$. With it the value increases with the code
  and commutes with the transports and base changes, so TC⁺ holds for these codes; also TC⁺♯ for long codes below $`\hat G + G_2`$. The referee: one case cites the pin with moved lower
  parameters ([SHIFT6.md](SHIFT6.md) §1.2) by name only, and the instance should be written out (m2); TC⁺♯ uses the value clause of a base-change lemma whose review called it thin, but no
  frontier uses TC⁺ (m4).
- **EXP-BOUND** (proved; the normal form of $`\hat\zeta_H`$ is a computer check). For every normal multiplier $`\zeta \lt \hat\zeta_H`$, every exponent of $`R_\lambda(\zeta)`$ is below $`\hat G + G_2`$, since
  $`R(\hat\zeta_H) = \omega^{\hat G + G_2}`$ by the closed form of READ ([SHIFT4.md](SHIFT4.md) §2.2). This replaces the check on 889 multipliers in the proof of $`X_{21}`$ ([SHIFT10.md](SHIFT10.md) §3.1). The
  referee: the case with constants needs the two-case argument of MARGIN, not MONO (m3).
- **The inventory** (proved, by reading). False as stated: the exact long formulas of [SHIFT2.md](SHIFT2.md) §3.1, [SHIFT3.md](SHIFT3.md) §1.1, §2.1, [SHIFT4.md](SHIFT4.md) §1.1 (also with the lh-shift) and
  §2.1 (EXACT-LONG-CL\*), [SHIFT5.md](SHIFT5.md) §1.1 (EXACT-LONG⁺) and §2.1 (EXACT-LONG$`^V`$, EXACT-LONG$`^G`$, and EXACT-F at $`m_0 \ge \Omega_1`$), and [SHIFT6.md](SHIFT6.md) §1.2 (EXACT-LONG$`^e`$, at every
  code of its range); the lower bound LB, the direction "$`\Leftarrow`$" of CROSS-O for $`x \ge 2`$ and of LONG-CLASS, and the lower ends of the brackets. They stand: every cap, every crossing in the
  direction "$`\Rightarrow`$", every "$`\le`$" half, PIN-ALL and the short exact values; with the corrected value: TC⁺ for long codes, MONO-F, the pin PIN$`^{(2)}`$, and CROSS-SHARP$`^{(3)\prime\prime}`$ (a) of
  [SHIFT5.md](SHIFT5.md) §2.1. NO-READL ([SHIFT5.md](SHIFT5.md) §2.1) is not proved as written.
- **The chain to $`X_{21}`$** (proved, by reading). $`X_9`$ to $`X_{18}`$, $`X_{19}^\flat`$ and $`X_{19}^{\mathrm{lin}}`$ stand as written (their caps use only short prefix atoms, with no crossing of a long restart
  and no base change); $`X_{19}`$, $`X_{20}`$ and $`X_{21}`$ stand with FAR-PIN$`^{L\sharp}`$ and EXP-BOUND. The referee read the proofs of $`X_{12}`$ to $`X_{15}`$, $`X_{18}`$ and $`X_{21}`$ and accepted the reading for
  $`X_9`$ to $`X_{11}`$, $`X_{16}`$ and $`X_{17}`$. So no range below $`X_{21}`$ is lowered.
- **$`R_2^S`$** (confirmed): $`[0, \upsilon_{\omega^3}]`$. A remark, not proved: when $`\nu_C = \nu_S`$ (now proved, §1.1), the two structures agree on every relation with right end at most $`\nu_S`$, and
  S-COVERED ([SHIFT9.md](SHIFT9.md) §1.2) would give $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^S)`$, so the claim in $`R_2^S`$ would reach past $`\upsilon_{\omega^3}`$.

### 1.3 Lean, stage 2: Carlson's core theorems, CP, and INC1

- **Files.** Ten new modules of [R2/](R2/) (Arith, CitedC09, CoreC, Move, CitedR1, Ups, R1Gap, CCF, Inc1, BlockC); six modules of stage 1 changed only in their doc comments (module
  names in place of file names). In the repository all of them build as modules with the whole library (green, no `sorry`), which settles the audit's point that they were checked only as one
  bundle. Details on [LEAN.md](LEAN.md).
- **No axiom:** Carlson 2009, L.4.4, L.4.5 and L.5.5 (7); Lemma MOVE.
- **From two cited theorems of Carlson 2009** (Thm 14.10 (1)–(3) for finite closed sets, Thm 14.14; the first axioms that mention $`R_2^C`$): an isominimal set is pointwise below each of its closed
  coverings; the core is an initial segment; every point of the core has a reach; the corollary of LOC without its hypothesis; Theorems CP\* and CP.
- **$`\upsilon`$:** the Lean $`\upsilon`$ satisfies the three clauses of Wilken 2020, Def 21.4, and is normal; $`\upsilon_n`$ and $`\upsilon_\omega`$ are countable.
- **Theorem INC1:** $`a \le_1 b`$ in $`R_2^C`$ and $`b \lt \Omega_1`$ give $`a \le_1 b`$ in $`R_1^+`$; with CC-F, LEFT (with a limit index), NOBAD, FANCOF, PI2-UP, RIGHT-LIM, RE-U and CLEAN-C, and no axiom about
  $`R_2^C`$. The proof uses [W07b] Cor 5.9 (finitely many $`\lt_1`$-predecessors in a gap) in place of the project's Lemma L, which makes it simpler.
- **First uses of FRAG and FRAG2 in $`R_2^C`$:** FRAG2 with the skeleton hypothesis reduced by INC1 and LEFT; FRAG with FRAG2; SK1 inside a block; $`\le_1`$ of $`R_2^C`$ equals $`\le_1`$ of $`R_1^+`$ below
  the first $`\lt_2`$-right end and on $`[0, \upsilon_\omega]`$.
- **13 new axioms** (1 constant, 12 facts), each a literal statement with its source: Carlson 2009, Thm 14.10 and Thm 14.14; [W07b] L.2.1 (twice), the remark after Thm 2.2, Cor 5.10 (twice),
  Def 5.8 with Cor 5.9, Claim 5.6; [W07a] Def 9.1 (the constant and its normality), Thm 3.23; Wilken 2020, Prop 21.6. In all there are 40 axioms (8 constants, 32 facts) in three files.
- **The audit**: all 13 axioms faithful (the Lean form of Claim 5.6 is weaker than the paper's, and the case of Thm 14.10 without $`0`$ follows from the case with $`0`$), all definitions right, every
  main theorem Lean-proved; no fatal and no blocking point. Minor points: [LEAN.md](LEAN.md) must name the three files (n1; done); CP uses only Thm 14.10, and CP′ adds Thm 14.14 (n2); build the
  modules one by one (n3; done); three facts on $`R_1^+`$ restate results of Wilken, AML 45 (2006), which we do not have, and their statements are in [W07b] §2 (n4); one doc line on the case
  without $`0`$ (n5).

### 1.4 Status after the forty-first round

- **Wilken's claim in $`R_2^C`$**: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, \nu_C]`$ given FRAG**, $`\nu_C = L(\omega+1)`$ (1 review, §1.1); $`[0, X_{21}]`$ has the repaired proof (1 review)
  and the audit's reading (§1.2); $`[0, X_{19}^{\mathrm{lin}}]`$ and $`[0, X_{18}]`$ have 2 reviews. **Not proved as written**: every range above $`\nu_C`$ recorded on [SHIFT7.md](SHIFT7.md) §3.2 to
  [SHIFT10.md](SHIFT10.md) §1.
- **Wilken's claim in $`R_2^S`$**: proved only up to $`\upsilon_{\omega^3}`$ (with or without FRAG). Given FRAG: $`\nu_S = \nu_C = L(\omega+1)`$, the two structures agree on every relation with right end
  below $`\nu`$, and $`R_2^C`$ has no ghost pair. The agreement above $`\nu`$ (up to $`Z^\varepsilon`$) is not proved as written. (E) is open, and $`\beta_0`$ is not located.
- **Reaches** (given FRAG): exact for every restart below $`\nu`$; for every code below $`P'`$ at levels 1 and 2, $`r(\lambda) = k_\lambda(\Theta_\lambda(m))`$.
- **LOW: false, given FRAG** (1 review); LOW$`^\infty`$ holds.
- **Lean**: $`R_2^C`$, the core, LOC, FRAG, FRAG2 (§3.3 of [SHIFT10.md](SHIFT10.md)); now also Carlson's core theorems (cited), CP, the Lean $`\upsilon`$ as Wilken's, INC1, and FRAG with FRAG2 in
  $`R_2^C`$ (§1.3).
- The lower-bound program below $`\theta_0`$: no change ($`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$, [SHIFT10.md](SHIFT10.md) §2.3; past $`S_*`$ the conjecture LEX-SELF). The step below SRO: no change
  (done for every $`n`$ on all 3,166 sample matrices; the general statement for all standard matrices below SRO is open).

### 1.5 Checks of the forty-first round

Each run was under 60 seconds; none is a proof.

- §1.1. Three checks with two seeds (readings, normal forms and order of the multipliers below $`\hat\zeta_3`$ and between $`\hat\zeta_3`$ and the next one), 0 failures. They do not test reaches,
  visibility, copies or pins. The referee ran no search.
- §1.2. Two runs (the witnesses: membership in the domain, normal forms, order below $`X_6`$ and $`X_{21}`$; the first run used a wrong base and is superseded), 0 failures. The referee's one search
  confirmed the witness of LB-b-FALSE under the hypothesis of the cited source.
- §1.3. Lean: the bundle of the ten new files green (the audit rebuilt it, identical, and parsed the axioms of 101 theorems); in the repository every file builds as a module with the whole
  library (green, no `sorry`; only warnings about unused variables).

### 1.6 Open

- Above $`\nu_C`$: the exact calculus in the gaps with the corrected values (the reaches of the points $`L(e)`$ and of the restarts with codes $`\ge P'`$); then the frontiers $`X_A`$ to $`Z^\Lambda`$ again,
  the $`R_2^S`$ side up to $`Z^\varepsilon`$, and one level up (Theorems C$`^{\mathrm{LL}}`$, C$`^{\mathrm{FP}}`$, $`\nu_3`$).
- The claim above $`\nu_C`$ given FRAG in $`R_2^C`$ (above $`X_4`$ without FRAG), and above $`\upsilon_{\omega^3}`$ in $`R_2^S`$ (first step: from $`\nu_C = \nu_S`$ to $`[0, \nu] \subseteq \mathrm{Core}(R_2^S)`$).
- Lean, in order: Lemma L (the chain bound in a gap); the first pair $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ in $`R_2^C`$ (it needs the segment compression of FRAG as a lemma of its own); Theorems B, B″,
  TOP, RS and SK3 below $`\upsilon_{\omega^3}`$; BLK$`^\Xi`$, BLK$`^O`$; SKEL⁺, CAP, LIFT-0, O$`^C`$, NU-CT and $`\nu_C`$; the $`R_2^S`$ side ([LEAN.md](LEAN.md)).
- $`R_2^S = R_2^C`$: (E), $`\beta_0`$, FAN-LOAD, and the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: chain number 3 past $`\varepsilon_{\Omega_\omega+1}`$; past $`S_*`$, capacities with $`\alpha \ge \Gamma_0`$ (conjecture LEX-SELF) or another way; then the tower of $`\Omega`$'s up to $`\theta_0`$;
  $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; the rest of [COVER.md](COVER.md) §9.
