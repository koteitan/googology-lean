[← Back](README.md) | [English](SHIFT11.md) | [Japanese](SHIFT11-ja.md)

# $`R_2^+`$, the forty-first to forty-third rounds: the exact long reach below $`P'`$, $`\nu_C = \nu_S = L(\omega+1)`$ again, the claim in $`R_2^C`$ up to $`Z^{\mathrm{FP}}`$ and in $`R_2^S`$ up to $`Z^\Lambda`$, and the restart blocks of $`R_2^C`$ in Lean

This page continues [SHIFT10.md](SHIFT10.md) (§3 there is the fortieth round); §1 is the forty-first round, §2 the forty-second and §3 the forty-third. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a fatal or blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known, or of the target, is not counted as progress.

## 1. The forty-first round

**Later (the forty-second round, §2):** the gap calculus above $`\nu_C`$ is run again on the corrected values, so, given FRAG, the claim holds in $`R_2^C`$ on $`[0, Z^\Lambda]`$
again (1 review), and the step TC⁺$`^\omega`$ for $`B_n`$ now cites EQ$`^{\mathrm{all}}`$ (§2.1); in $`R_2^S`$ the claim holds on $`[0, F_\nu)`$, past $`\nu_C`$ (§2.2). **Later (the forty-third round, §3):** the claim holds in $`R_2^C`$ on $`[0, Z^{\mathrm{FP}}]`$ and in $`R_2^S`$ on $`[0, Z^\Lambda)`$, given FRAG. The open list is §3.6.

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

## 2. The forty-second round

**Later (the forty-third round, §3):** the exact reach of level 3 is proved below $`Z^{\mathrm{FP}}`$ for long codes too, FALSE-LB″ is proved, and given FRAG the claim holds in $`R_2^C`$ on $`[0, Z^{\mathrm{FP}}]`$, $`Z^{\mathrm{LL}}`$ included (§3.1); the claim in $`R_2^S`$ on $`[0, Z^\Lambda)`$, conditional in §2.2, is proved (§3.2).

Three papers (2026-10): the gap calculus above $`\nu_C`$ run again on the corrected values (§2.1) and the $`R_2^S`$ side on the corrected values (§2.2), each refereed once, and the third Lean
stage for $`R_2^C`$ (§2.3), whose audit checked the axioms and the definitions. A result in this section has 1 review unless a count is given. Levels are numbered as in §1 (one higher than in the
papers): the gap restarts $`H(\eta_e + \xi)`$, $`0 \lt \xi \lt P'`$, are at level 2, and the points $`L(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$ are the restarts of level 3.

**The frontier in $`R_2^C`$ is back at $`Z^\Lambda`$.** Given FRAG, **Wilken's claim holds in $`R_2^C`$ on $`[0, Z^\Lambda]`$, both halves**, with

```math
Z^\Lambda = L(\theta'_2\cdot\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2}),\qquad \theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2),
```

and $`\beta_0 \gt Z^\Lambda`$ (the two structures agree on every relation with right end below $`Z^\Lambda`$) and $`T_3^C \gt Z^\Lambda`$ (1 review of the re-run, §2.1). The ranges of
[SHIFT7.md](SHIFT7.md) §3.2 to [SHIFT10.md](SHIFT10.md) §1 up to $`Z^\Lambda`$ come back as restrictions of this theorem. $`Z^{\mathrm{LL}}`$ does not come back. **In $`R_2^S`$ the claim now holds on $`[0, F_\nu)`$**, given
FRAG, with

```math
F_\nu = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P' + \omega^{P+\Omega_1}) \gt \nu_C,
```

so it passes $`\upsilon_{\omega^3}`$ and $`\nu_C`$ (1 review, §2.2; it rests on EQ$`^{\mathrm{all}}`$ of §2.1).

Papers cited: in §2.1 and §2.2 only through refereed stages: [W07b] (L.2.1, Thm 2.2, Cor 5.10), Carlson 2009 (Def 5.3, L.5.5, L.5.7 (3), Thm 14.14), Wilken 2020 (Prop 21.6, L.21.7, L.21.10,
L.21.12, Prop 21.11), and in §2.2 also [C11] and [CW12b] (Prop 7.1, Prop 7.4, L.7.5). In §2.3: [W07a] (Def 3.28) and [W07b] (Def 4.1, L.4.5, Thm 5.3). None uses Wilken, JSL 72 (2007),
Carlson, AML 38 (1999), or Wilken, AML 45 (2006).

The minor points of the reviews of the forty-first round are applied in the paper of §2.1: the point m1 of the review of §1.1 ((EQ) for the maps that raise constants, proved after the
theorem) is now a theorem of its own, EQ$`^{\mathrm{all}}`$, refereed in this round, and the points m2–m8 are written into the proof. The points n2 and n5 of the audit of §1.3 are applied in
Lean (§2.3).

### 2.1 The gap calculus above $`\nu_C`$ on the corrected values, and the claim in $`R_2^C`$ on $`[0, Z^\Lambda]`$

- **Theorem EQ$`^{\mathrm{all}}`$** (proved, given FRAG). Let $`T`$ be a base change of the class BC$`^\pi`$ ($`T^U`$, $`T''_g`$, $`B_n`$, $`B'_n`$, the pieces of a FRAG″ map, the transports between regions of
  level 3, and also the maps that raise constants), $`\lambda`$ a restart of level 1 or 2 such that $`\lambda`$ and $`T\lambda`$ have their exact reaches, and $`c \le m_\lambda`$ a code whose data lie in the domain
  of $`T`$, with no absorption at $`T\lambda`$. Then $`T(A^\sharp_\lambda(c)) = A^\sharp_{T\lambda}(c^T)`$, where $`A^\sharp_\lambda(c) = k_\lambda(\Theta_\lambda(c))`$; so $`T(r(\lambda)) = r(T\lambda)`$. The proof runs after ENUM-REACH
  (§1.1), by induction on the source code; the image code may be larger, and its values come from the finished theorem, never from the induction. This closes the point m1 of the review of
  §1.1: TC⁺$`^\omega`$ for $`B_n`$ now cites EQ$`^{\mathrm{all}}`$, so the chain to $`\nu_C = \nu_S = L(\omega+1)`$ is complete as written. The referee: the induction is well-founded; at the image only
  the images of the prefixes of the Cantor normal form of the source can shadow. Minor points: enlarge the finite set of FRAG″ by all the data of the value, not only by the hereditary
  parameters of $`r(R)`$ (n5); the hypothesis must ask for CAP♯ at every long restart of the interval at the image, which the gap calculus supplies (n6); above $`\nu_C`$ the equivariance of $`F`$ is
  cited through the relativized tools (n7); the condition "no absorption" is about the exponent of the image restart, and holds (n3).
- **VAL-IF** (proved, by reading). In the written proofs of the frontiers above $`\nu_C`$ ([SHIFT8.md](SHIFT8.md) to [SHIFT10.md](SHIFT10.md)) a reach of a restart of level 1 or 2 enters only
  through five items: V0 the milestone $`\nu_C = \nu_S = L(\omega+1)`$; V1 the conclusion of the gap calculus GAP-CALC$`^{\mathrm{reg}}`$; V2 the equivariance of gap reaches under base changes; V3 the
  pins at relative bases (the far pin FAR-PIN″); V4 the exact reaches of the crossed gap restarts in CROSS-LIM″ (its hypothesis (H4)). The referee searched the texts for every broken formula
  and found every hit in V0–V4, in a remark, or in an open part.
- **Theorem GAP-CALC$`^{\sharp\mathrm{reg}}`$** (proved by transfer, given FRAG). ENUM-REACH above a base point $`p`$ with a bound $`y`$: if every new $`\lt_2`$-pair with right end in $`(p, y)`$ is a
  $`\tau`$-$`\delta`$ pair, then every gap restart $`R`$ with $`p \lt \rho_R \lt \min(y, \psi_{\Omega_1}(\Omega_\omega\cdot 3))`$ and the region condition (REG♯) has $`r(R) = k_R(\Theta_R(m_R))`$ (both halves), with
  $`r(R) \lt H(\eta_R + \omega^{\ell(m_R)}) \le L(e+1)`$ (CAP♯), the strict bound LC-STRICT♯, CROSS♯, the pins, and $`R`$ does not cross itself. Here $`\ell(m) = 2`$ for a short code and $`\ell(m) = l(m) + 1`$
  for a long one ($`l(m)`$ the leading exponent), and (REG♯) says $`H(\eta_R + \omega^{\ell(m_R)}) \le y`$: it is read from the code alone, so it can be checked before the theorem, and it passes to the
  smaller restarts. (The old condition used the old offset, which the corrected value no longer gives.) The referee: every relation that the count reads has its right end in $`(p, y)`$, so the
  count is safe; the weaker form $`r(R') \gt R_1`$ of (LONG) is enough. Minor points: BOUND♯ is an equality for short codes, not a strict bound (n1; nothing uses the strict form); one step of
  the heredity is false for infinite codes, but the needed bound $`\ell(m') \lt e_R`$ holds (n8).
- **FAR-PIN″♯** (proved by transfer, given FRAG). The far pins one level up ([SHIFT9.md](SHIFT9.md), [SHIFT10.md](SHIFT10.md) §1) with the corrected atoms. Minor point n2: the bound
  "the lower parameters are at least $`L(e)`$" is needed only for the copies built inside the gap calculus; a given copy keeps its own atoms.
- **The skeleton steps** (proved by transfer, given FRAG): CROSS-LIM″♯, PAIR$`_j`$♯, LOW$`_j`$♯, C-TRANSFER♯, TC⁺″♯ and TRANS-K″♯. CROSS-LIM″ reads the exact reaches of the crossed long gap
  restarts (codes such as $`G_2\cdot 2`$ and $`G_2 + P`$) and their images under $`T^U_\mu`$; PAIR$`_j`$ uses $`B'_n`$, which raises constants, so it needs EQ$`^{\mathrm{all}}`$; LOW$`_j`$ and C-TRANSFER use only upper
  bounds (LC-STRICT♯); TRANS-K″ needs the equivariance only at the finitely many roots. Minor points: CROSS-LIM″ moves $`L(e)`$, so it must cite EQ$`^{\mathrm{all}}`$ alone (n2); the region condition at
  the realizer $`\mu`$ of code exactly $`G(\zeta_{k+1})`$ uses the whole-gap form (n4).
- **Theorem C$`^{\Lambda\sharp}`$ and the claim on $`[0, Z^\Lambda]`$** (proved by transfer, given FRAG). For every region of level 3 below $`\theta'_2\cdot\omega^2`$: the new pairs are exactly
  $`(L(\lambda''+\omega j), L(\lambda''+\omega j+1))`$, $`j \ge 1`$; the gap calculus holds in every gap; $`L(\lambda'')`$ has an exact reach; every restart of the region has an exact reach. So $`\beta_0 \gt Z^\Lambda`$,
  $`T_3^C \gt Z^\Lambda`$, no fan apex and no triple nest lie below $`Z^\Lambda`$, $`[0, Z^\Lambda] \subseteq \mathrm{Core}(R_2^C)`$, and $`Z^\Lambda`$ is an InaccPsi normal form with collapse arguments below $`I_\omega`$.
- **The frontiers in order** (each a restriction of C$`^{\Lambda\sharp}`$, both halves, proved by transfer): $`X_A`$, $`L(\omega^2)`$, $`L(\Omega_1\cdot\omega)`$, $`L(\varepsilon_{\Phi_\Omega+1})`$, $`L(G_2)`$,
  $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$, $`Z^\Gamma`$, $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$, $`Z^\varepsilon`$, $`Z^\Lambda`$ (names as in [SHIFT7.md](SHIFT7.md) §3.2 to [SHIFT10.md](SHIFT10.md) §1). Where the
  corrected value is needed: $`X_A`$ only through the milestone; $`L(\omega^2)`$ at (H4) of CROSS-LIM″ (the crossed long codes, such as $`G_2\cdot 2`$, whose old value is false) and at $`B'_n`$ in PAIR;
  $`L(\Omega_1\cdot\omega)`$ to $`L(G_2)`$ only in the skeleton steps; from $`L(\Omega_2+\Phi^{P'}\cdot\omega)`$ on, the reach proofs of level 3 pin through long gap restarts (FAR-PIN″♯, TC⁺″♯, TRANS-K″♯).
- **Level 3, short codes** (proved). For every restart $`b = L(\lambda'')`$ below $`Z^\Lambda`$ with code $`c''`$ (every code below $`G''(\omega^2)`$):

```math
r(b) = k''_b(o_b(c'')),
```

  the $`o_b(c'')`$-th point at or above $`L(\lambda''+\omega+1)`$ that is closed relative to $`b`$ (no point of $`(b, y]`$ reaches past $`y`$), with $`o_b`$ the reading at $`b`$: the form of ENUM-REACH one level
  up. Below $`Z^\Lambda`$ no reach of level 3 crosses a restart of level 3, so the shadowing of §1.1 does not occur there.
- **Not recovered** (open). $`Z^{\mathrm{LL}}`$ (Theorem C$`^{\mathrm{LL}}`$): its lower bound copies the landing of the $`D`$-part one level up, which is false one level down. Conjecture FALSE-LB″: at a
  restart $`b = L(\lambda'')`$ of code $`G''(\omega^2)\cdot 2`$, $`r(b) = L(\lambda''+\omega^2+\omega+1) + L(\lambda''+\omega^2)`$, so that lower bound fails at $`D = 2`$. Conjecture ENUM-REACH″: $`r(b) = k''_b(o_b(c''))`$ for
  every code $`c''`$ below $`P_3 = \psi_{\Omega_2}(\Omega_\omega\cdot 3)`$, long codes included (open for every long code of level 3).
- **$`R_2^S`$ up to $`Z^\varepsilon`$ along this re-run**: an outline (the author found only V1 and V2 in those proofs by a search, and did not read them line by line). Not counted.
- **The weakest steps** (named by the author): the test of visibility at the image in EQ$`^{\mathrm{all}}`$; the count of closed points inside a gap; the pins with corrected atoms where an image
  is a point $`L(e)`$.

### 2.2 $`R_2^S`$ on the corrected values: $`[0, \nu_C]`$ and a step past it

Write $`\mathrm{LL}`$ for the set of countable restarts $`R`$ whose set $`\mathrm{Pred}_1(R)`$ of $`\le_1`$-predecessors is cofinal in $`R`$ (in $`R_2^S`$), and $`x_{\mathrm{cof}}(p)`$ for the least element of
$`\mathrm{LL}`$ above $`p`$. An **admissible base** is a point $`p`$ with a finite $`B \subseteq [0, p]`$ such that $`\beta_0 \gt p`$, every $`\alpha \le p`$ outside $`B`$ has its reach at most $`p`$, every $`b \in B`$ has
$`\mathrm{Pred}_1(b)`$ bounded below $`b`$, and $`R_2^S`$ has no triple nest with top at most $`p`$.

- **$`\beta_0 \gt \nu_C`$, and the claim in $`R_2^S`$ on $`[0, \nu_C]`$** (proved, given FRAG). If $`\beta_0 = \nu`$, the only possible extra left end is $`L(\omega)`$ (Carlson 2009, L.5.5 (6)), and
  $`L(\omega) \lt_2 \nu`$ holds in $`R_2^S`$. Then $`[0, R_1) \subseteq \mathrm{Core}(R_2^S)`$ with $`R_1 = H(\eta_\nu + \omega^2)`$ the next restart point above $`\nu`$ (LOC-ISO; $`R_1`$ has no $`\le_1`$-predecessor).
  This is the step from $`\nu_C = \nu_S`$ to $`[0, \nu] \subseteq \mathrm{Core}(R_2^S)`$ that §1.6 asked for.
- **Theorem X-COF** (proved, without FRAG, for an admissible base). For every admissible base $`p`$: $`x_{\mathrm{cof}}(p)`$ exists, $`\beta_0 \gt x_{\mathrm{cof}}(p)`$, $`T_3^C \gt x_{\mathrm{cof}}(p)`$, and every
  $`\lt_2^S`$-pair with right end in $`(p, x_{\mathrm{cof}}(p)]`$ is a $`\tau`$-$`\delta`$ pair. It reads no reach above $`p`$. The referee: the case split of the extra left end is complete, and Carlson's
  clause 2 at the $`\tau`$-points above $`\nu`$ needs no gap calculus there (an earlier citation of it was not needed).
- **Lemma E1$`^p`$** (proved, without FRAG). A restart $`z \gt p`$ with no element of $`\mathrm{LL}`$ in $`(p, z)`$ and a countable last exponent $`e_z`$ reaches at most $`\delta_z + (-1 + e_z) \lt R_{1,z}`$. So
  for an admissible base $`p = L(e_p)`$ every restart in $`(p, H(\eta_p + \Omega_1)]`$ has its $`\le_1`$-predecessors in $`B`$, and $`x_{\mathrm{cof}}(p) \ge H(\eta_p + \omega^{\Omega_1+1})`$. Minor point m4: the copy keeps $`+`$
  because $`R_2^S`$ is read in the language with $`+`$.
- **The instance $`p = \nu`$** (proved, given FRAG). $`\beta_0 \gt x_{\mathrm{cof}}(\nu) \ge Q_\nu`$, $`T_3^C \gt Q_\nu`$, the claim in $`R_2^C`$ on $`[0, Q_\nu]`$ and **the claim in $`R_2^S`$ on $`[0, F_\nu)`$**, with
  $`Q_\nu = H(\eta_\nu + \omega^{\Omega_1+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P' + \omega^{P+\Omega_1+1})`$ and $`F_\nu = H(\eta_\nu + \Omega_1)`$. The part in $`R_2^C`$ is below $`Z^\Lambda`$ (§2.1), but it
  does not use the gap calculus above $`\nu_C`$.
- **The blocking point B-1 of the review, and how it is met.** The referee found the proofs of the two items above (and of $`\beta_0 \gt \nu_C`$) correct relative to the milestone $`\nu_C = \nu_S = L(\omega+1)`$,
  but the paper called them "robust (milestone only)", while the milestone needs EQ$`^{\mathrm{all}}`$ for $`B_n`$ (point m1 of the review of §1.1). So the record must name that dependence. EQ$`^{\mathrm{all}}`$ is
  proved in §2.1 (1 review), so we record them as proved, given FRAG and EQ$`^{\mathrm{all}}`$. B-1 is about the label, not about a step of the proof.
- **UNIFORM-B** (proved, given its two hypotheses). For a bound $`b`$: if the reaches of the gap restarts below $`b`$ obey their caps (CAP♯, LC-STRICT♯), and every point $`L(e) \lt b`$ of
  $`\mathrm{LL}`$ reaches $`L(e+1)`$ and makes the pair $`L(e) \lt_2 L(e+1)`$ in $`R_2^S`$, then $`\beta_0 \ge b`$ and $`T_3^C \ge b`$. With FIN-CROSS (by the caps alone, the elements of $`\mathrm{LL}`$ below $`b`$ are
  points $`L(e)`$ of limit index) and K2$`^{\mathrm{cap}}`$. So the exact long values enter only through those pairs (PAIR, which needs EQ$`^{\mathrm{all}}`$). Minor points: K2$`^{\mathrm{cap}}`$ must use one more copy
  point in place of a citation whose hypothesis the caps do not give (m1); the sentence on Carlson's criterion holds only for right ends in $`(p, b)`$ (m2).
- **Conditional, not counted** (the referee checked only the labels): along §2.1, the claim in $`R_2^S`$ on $`[0, Z^\Lambda)`$, and $`\beta_0 \gt Q^\Lambda`$ with the claim in $`R_2^C`$ on $`[0, Q^\Lambda]`$, where
  $`Q^\Lambda = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{P'+1} + P' + \omega^{P+\Omega_1+1})`$ (minor point m3: name the bound point and the form of the region condition).
- **The status of the earlier $`R_2^S`$ results** (the author's reading; the referee checked samples, which agree, and did not re-check the whole table, so it is not counted): the general lemmas
  (MIN$`^S`$, LOC-ISO, S-COVERED, the fan lemmas and others) stand; the frontiers up to $`Z^\Lambda`$ come back with the corrected values through §2.1; the results on $`Z^{\mathrm{LL}}`$ and above stay broken.

### 2.3 Lean, stage 3: Lemma L, the first pair, and the blocks below $`\upsilon_{\omega^3}`$

- **Files.** Eight new modules of [R2/](R2/) (CitedL, ChainL, BaseC, Pair1, BlockB, RstC, Blk3, RS), and CitedC09 with one more doc line (point n5 of the audit of §1.3). In the repository
  all of them build as modules with the whole library (green, no `sorry`). Details on [LEAN.md](LEAN.md).
- **Lemma L** (`chain_bound`): for $`\tau \in \{1\} \cup E`$ and $`z_0 \in T^\tau \cap (\tau, \Omega_1)`$, a chain $`z_0 \lt_1 z_1 \lt_1 \dots \lt_1 z_k`$ of $`R_1^+`$ has $`k \le \mathrm{ht}_\tau(z_0) + 1`$; also inside a gap.
- **Theorem A in $`R_2^C`$** (`thmA_C`): $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ is the least pair, $`\upsilon_\omega`$ is the only $`\lt_2`$-predecessor of $`\upsilon_{\omega+1}`$, $`\le_1`$ is that of $`R_1^+`$ up to
  $`\upsilon_{\omega+1}`$, and no point at most $`\upsilon_{\omega+1}`$ is $`\le_1`$ to a point above it. The compression of segments is a lemma of its own, COMP-C (`comp_c`), proved to be a covering of $`R_2^C`$;
  it uses Theorem CC-F and the inverse base change, not the compression step of FRAG.
- **Theorem B** (`thmB_C`): below $`\upsilon_{\omega\cdot\omega}`$ the $`\lt_2`$-pairs are exactly $`(\upsilon_{\omega(j+1)}, \upsilon_{\omega(j+1)+1})`$; the blocks are closed, and inside each block $`\le_1`$ is that of $`R_1^+`$.
- **Theorem B″ with TOP** (`thmB2_C`), for every restart $`\rho_h = \upsilon_{\omega^2 h}`$ below $`\upsilon_{\omega^3}`$ (in Lean the index is $`h - 1`$): no point below $`\rho_h`$ is $`\le_1`$ to a point at or above it,
  $`\rho_h`$ has no $`\lt_2`$-successor, $`\rho_h \le_1 \gamma`$ for $`\gamma \in [\rho_h, \delta_h]`$, $`\rho_h`$ is not $`\le_1`$ to any point above $`\delta_h + 1`$, and the later blocks.
- **RS** (`rs_h`, `reach_rst`): $`\mathrm{lh}(\rho_h) = \delta_h + 1`$, with the Lean FRAG of stage 1.
- **The pairs below $`\upsilon_{\omega^3}`$** (`pairs_lt_w3`): exactly $`(\upsilon_\xi, \upsilon_{\xi+1})`$ with $`\xi = \omega^2 h + \omega j + \omega`$; and **SK3** (`sk3_C`): below $`\upsilon_{\omega^3}`$ every point that is not a
  $`\upsilon`$-point has the reach it has in $`R_1^+`$.
- **4 new axioms** (1 constant, 3 facts) in the new file CitedL: `lhT` ([W07b] Def 4.1), `lh_eq_lhT` ([W07b] Thm 5.3), `ht_lhT_lt` ([W07b] L.4.5), `Par_sub` ([W07a] Def 3.28; stated for
  $`\tau \in E`$ only). In all there are 44 axioms (9 constants, 35 facts) in four files: Cited, CitedR1, CitedC09, CitedL. The main theorems use 35 of them, RS uses 41, and none uses an axiom of
  CitedC09.
- **The audit**: the four axioms faithful, every definition right, every main theorem Lean-proved; a false statement added at the end of a bundle made the check fail, so the short checks
  read the whole file. No fatal and no blocking point. Minor points: do not copy a stray scratch file (m1; not copied); the axiom counts leave out Lean's three standard axioms (m2); the
  index shift of `thmB2_C`, `rs_h`, `reach_rst` and the range of `Par_sub` are written on [LEAN.md](LEAN.md) (m3); build the modules in the repository (m4; done).

### 2.4 Status after the forty-second round

- **Wilken's claim in $`R_2^C`$**: both halves on $`[0, X_4]`$ without FRAG, and **on $`[0, Z^\Lambda]`$ given FRAG** (1 review of the re-run, §2.1), $`Z^\Lambda = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2})`$;
  $`[0, \nu_C]`$ has the proof of §1.1 with EQ$`^{\mathrm{all}}`$ (1 review each), $`[0, X_{21}]`$ the repaired proof (1 review), and $`[0, X_{19}^{\mathrm{lin}}]`$ and $`[0, X_{18}]`$ 2 reviews. Above $`Z^\Lambda`$
  (from $`Z^{\mathrm{LL}}`$ on): not proved.
- **Wilken's claim in $`R_2^S`$**: on $`[0, \upsilon_{\omega^3}]`$ (with or without FRAG), and, given FRAG, on $`[0, F_\nu)`$, past $`\nu_C`$ (1 review, §2.2). $`\beta_0 \gt Z^\Lambda`$ given FRAG. (E) is open, and
  $`\beta_0`$ is not located.
- **Reaches** (given FRAG): $`r(\lambda) = k_\lambda(\Theta_\lambda(m))`$ for every code below $`P'`$ at levels 1 and 2, below $`\nu_C`$ and, with (REG♯), in the gaps above any base point below
  $`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$; it commutes with every base change of the class BC$`^\pi`$ (EQ$`^{\mathrm{all}}`$); at level 3, $`r(b) = k''_b(o_b(c''))`$ for every restart below $`Z^\Lambda`$.
- **LOW: false, given FRAG** (§1.1, 1 review); not touched in this round.
- **Lean**: as in §1.4, and now Lemma L, Theorems A, B, B″ with TOP, RS and SK3 in $`R_2^C`$ below $`\upsilon_{\omega^3}`$ (§2.3).
- The lower-bound program below $`\theta_0`$: no change ($`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$; past $`S_*`$ the conjecture LEX-SELF). The step below SRO: no change (done for every $`n`$ on all
  3,166 sample matrices; only the general statement for all standard matrices below SRO is open).

### 2.5 Checks of the forty-second round

Each run was under 60 seconds; none is a proof.

- §2.1. No run (the names from $`X_A`$ to $`Z^\Lambda`$ are normal forms ordered by the checks of earlier rounds). The referee ran no search: the weak points are about the hypotheses of
  cited lemmas, and the ordinal arithmetic was checked by hand.
- §2.2. Six runs on the terms (normal forms, order and codes of the points from $`\nu`$ to $`L(\omega+2)`$, among them $`R_1`$, $`F_\nu`$, $`Q_\nu`$, and of the points above $`Z^\Lambda`$ up to $`Q^\Lambda`$; one run was
  repeated after an ordering error of the author), 0 failures. The referee ran none.
- §2.3. Lean: each of the eight modules alone and all together, green (the audit re-ran them); the repository build of the whole library is green, with no `sorry`.

### 2.6 Open

- Above $`Z^\Lambda`$: the long codes of level 3 (Conjecture ENUM-REACH″, FALSE-LB″), the landing calculus of level 3, then Theorem C$`^{\mathrm{LL}}`$ and $`Z^{\mathrm{LL}}`$ again; the codes below
  $`P_3`$ and the next level ($`\nu_3`$).
- The claim above $`Z^\Lambda`$ given FRAG in $`R_2^C`$ (above $`X_4`$ without FRAG), and above $`F_\nu`$ in $`R_2^S`$ (the $`R_2^S`$ side up to $`Z^\Lambda`$ along §2.1 is conditional; up to
  $`Z^\varepsilon`$ an outline).
- Lean, in order: the restart blocks (BLK$`^\Xi`$, BLK$`^O`$; from $`\lambda = \omega^3`$ on the reach is $`\delta_\lambda + c^*(\lambda)`$ with an offset above 1, so the step "nothing at most $`\delta + 1`$ reaches past
  $`\delta + 1`$" fails, and RS$`_\lambda`$ needs the proof of [REACHES.md](REACHES.md) §1, not FRAG alone); SKEL⁺, CAP, LIFT-0, O$`^C`$, NU-CT and $`\nu_C`$; the $`R_2^S`$ side.
- $`R_2^S = R_2^C`$: (E), $`\beta_0`$, FAN-LOAD, and the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible (not worked on in this round): past $`S_*`$, capacities with $`\alpha \ge \Gamma_0`$ (conjecture LEX-SELF) or another way; then the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past
  $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; the rest of [COVER.md](COVER.md) §9.

## 3. The forty-third round

Three papers (2026-10): the exact reaches of level 3 below $`Z^{\mathrm{FP}}`$ (§3.1) and the $`R_2^S`$ side up to $`Z^\Lambda`$ with an induction above it that reads only caps (§3.2), each refereed once,
and the fourth Lean stage for $`R_2^C`$ (§3.3), whose audit checked the axioms and the definitions. A result in this section has 1 review unless a count is given. Levels are numbered as in §1
(one higher than in the papers): the restarts $`L(\lambda'')`$ are at level 3, and the points $`L_3(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + P_3\cdot e)`$ of [SHIFT10.md](SHIFT10.md) §2.1 are the restarts of level 4.

**The frontier in $`R_2^C`$ moves to $`Z^{\mathrm{FP}}`$.** Given FRAG, **Wilken's claim holds in $`R_2^C`$ on $`[0, Z^{\mathrm{FP}}]`$, both halves**, with

```math
Z^{\mathrm{FP}} = L(\theta'_2\cdot\Omega_2+\omega^{\hat G''+G''(\omega^2)}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\hat G''+G''(\omega^2)}),\qquad \hat G'' = G''(\Omega_2) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2}),
```

and $`\beta_0 \gt Z^{\mathrm{FP}}`$ and $`T_3^C \gt Z^{\mathrm{FP}}`$ (1 review, §3.1). $`Z^{\mathrm{LL}}`$ comes back as a restriction, and the conjecture FALSE-LB″ of §2.1 is now proved. The step from $`Z^\Lambda`$ to
$`Z^{\mathrm{LG}} = L(\theta'_2\cdot\omega^2 + \omega^{G''(\omega^2)+1})`$ has a second proof that uses no exact reach of level 3 (§3.2), so it has **2 reviews**. **In $`R_2^S`$ the claim now holds on $`[0, Z^\Lambda)`$**,
given FRAG (1 review, §3.2; it rests on §2.1). The point $`\nu_3`$ is not reached.

Papers cited: in §3.1 and §3.2 only through refereed stages: [W07b] (L.2.1), Carlson 2009 (Def 5.3, L.5.5, L.5.7 (3), Thm 14.14), Wilken 2020 (Prop 21.6, L.21.10, Prop 21.11, Thm 21.13), and in
§3.2 also [C11] and [CW12b] (Prop 7.1, L.7.5). In §3.3: Carlson 2009 (Thm 14.14) and the facts of [W07a] and [W07b] already cited in Lean. None uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999),
or Wilken, AML 45 (2006).

The minor points of the reviews of the forty-second round are applied: n1–n9 of the review of §2.1 in the paper of §3.1 (n8 with a new proof of the bound $`\ell(m') \lt e_R`$), B-1 and m1–m5 of the
review of §2.2 in the paper of §3.2, and m3 of the audit of §2.3 in Lean (§3.3).

### 3.1 The exact reach of level 3 below $`Z^{\mathrm{FP}}`$, FALSE-LB″, and the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{FP}}]`$

Notation as in §2.1 and [SHIFT10.md](SHIFT10.md) §2.1. For a restart $`b = L(\lambda'')`$ of level 3: $`L(\lambda''+\omega^2)`$ is the next restart point, $`F''_b = L(\lambda''+\Omega_1)`$, $`o_b`$ is the reading at $`b`$, and
$`k''_b`$ enumerates the points $`y \ge \delta''_1(b)`$ that are closed relative to $`b`$. A code is short if it is below $`G''(\omega^2)`$, and long otherwise.

- **READ$`^{\mathrm{FP}}`$ and RANGE″** (proved, without FRAG). A code $`c''`$ in $`[G''(\omega^2), \hat G'')`$ is $`G''(\omega^2)\cdot D + m_0`$ with $`D \ge 1`$, $`m_0 \lt G''(\omega^2)`$, and
  $`o_b(c'') = L(\lambda''+\omega^2)\cdot x_D + o_b(m_0)`$ with $`x_D = o_b(D)`$; a code $`\hat G'' + m_0`$ has $`o_b(c'') = F''_b + o_b(m_0)`$. Every restart of level 3 in $`(b, o_b(c'')]`$ has a short code, so **below
  $`Z^{\mathrm{FP}}`$ no long restart of level 3 is crossed**. The landing is $`\nu = L(\lambda''+\omega^2\cdot x^*)`$, $`x^*`$ the largest $`x`$ with $`L(\lambda''+\omega^2\cdot x) \le o_b(c'')`$; then $`x^* \le x_D`$, and $`x^* \lt x_D`$ when
  $`x^* \ge 2`$, so for $`x_D \ge 2`$ the landing lies strictly below the old landing $`L(\lambda''+\omega^2\cdot x_D)`$. For the codes $`\hat G''+m_0`$ the landing is $`F''_b`$.
- **NEST″, COUNT♯″, LAND″♯ and SHADOW-PREFIX″** (proved, without FRAG, given the reaches of the restarts crossed): the count of §1.1 one level up. The closed points of $`b`$ are counted region by
  region over the visible restarts, and a restart is shadowed only through one of the finitely many long prefix restarts of its index. They hold for every code; beyond $`Z^{\mathrm{FP}}`$ the
  other half of ENUM-REACH one level up (the reading past $`\hat G''`$, BOUND♯, the relative pins, crossings of long restarts) is open.
- **Theorem ENUM-REACH″$`^{\mathrm{FP}}`$** (proved by transfer, given FRAG). For every restart $`b = L(\lambda'')`$ of level 3 below $`Z^{\mathrm{FP}}`$, with code $`c''`$: $`r(b) = k''_b(o_b(c''))`$, both halves.
  For a long code $`r(b) = k''_\nu(t_\nu + s'')`$, with $`\nu`$ the landing, $`t_\nu`$ the reading of the code of $`\nu`$ at $`\nu`$ and $`s'' = -\nu + o_b(c'')`$. In particular, for the codes in
  $`[G''(\omega^2), G''(\omega^2)^2)`$: $`r(b) = \delta''_1(L(\lambda''+\omega^2)) + 1 + (-L(\lambda''+\omega^2) + o_b(c''))`$, and for the codes $`\hat G'' + m_0`$: $`r(b) = \delta''_1(F''_b) + F''_b + o_b(m_0)`$. Also the order
  of the values (MONO♯″), $`r(b) \ge o_b(c'')`$ (CROSS♯″), the sharp crossing rule (SHARP-CROSS″) and the cap $`r(b) \lt`$ the restart point after the landing (CAP♯$`^{\mathrm{FP}}`$). The whole code, its
  part $`m_0`$ too, is read at $`b`$, not at a landing: this is the repair that the fatal point F-1 of [SHIFT10.md](SHIFT10.md) §2.1 asked for, and it gives the two values of F-1 (codes
  $`G''(\omega^2)+\Omega_1`$ and $`\hat G''+\Omega_1`$: $`r(b) = \delta''_1(L(\lambda''+\omega^2)) + b`$ and $`r(b) = \delta''_1(F''_b) + F''_b + b`$). The referee re-derived the reading and the landing and recomputed
  seven values by hand. Minor points: the "$`\le`$" half needs the finite set of the far top lemma enlarged by the parameters of $`s''`$ in $`[b, \nu)`$, which the far pins allow (the same enlargement
  was accepted one level down) (m1); the equivariance EQ″ is proved for the far transport only, and nothing uses it for other maps (m2); the successor rule of COUNT♯″ at $`b`$ itself (m6).
- **FALSE-LB″** (proved, given FRAG). At the code $`G''(\omega^2)\cdot 2`$: $`r(b) = L(\lambda''+\omega^2+\omega+1) + L(\lambda''+\omega^2) \lt L(\lambda''+\omega^2\cdot 2)`$, the value of the conjecture of §2.1. Its
  "$`\le`$" half alone refutes the lower bound LB″. So these results of [SHIFT10.md](SHIFT10.md) are **false** where the corrected value differs, and their verdicts are withdrawn: LB″ and
  EXACT-LONG-CL″\* of §1.1 (for $`x_D \ge 2`$, and for $`D = 1`$ with $`m_0 \ge \Omega_1`$), and in §2.1 LB″$`^G`$, CROSS″ in its strong form, CROSS-O″ (for $`x \ge 2`$), EXACT-LONG″$`^G`$, EXACT-F″ (for
  $`m_0 \ge \Omega_1`$) and the single value of AGREE″. The review of §2.1 there had called LB″$`^G`$ and the strong CROSS″ proved; their proofs read the old values at the smaller codes
  $`G''(\omega^2)\cdot D' + f`$, which carry $`b`$ to $`L(\lambda''+\omega^2\cdot 2)`$, while the corrected values do not. Every $`m_0 \ge \Omega_1`$ is affected, $`P'`$ included (that review had listed $`P'`$ as
  not affected). **Stand:** PIN-ALL″, TOP-REG-FAR″, LONG″-$`G''(\omega^2)`$ and CROSSED″ of §1.1 there; the code side, the far pins, R-CAP″$`^G`$, CROSS-F″ and the weak form
  $`r(b) \ge L(\lambda''+1+o_b(\zeta))`$ of CROSS″ in §2.1 there; RANGE$`^{\mathrm{FP}}`$ and CAP-0″ below $`Z^{\mathrm{FP}}`$. Minor: one sentence must say which parts of CROSSED″$`^F`$ stand (m7).
- **Theorems C$`^{\mathrm{LL}\sharp}`$ and C$`^{\mathrm{FP}\sharp}`$, and the claim on $`[0, Z^{\mathrm{FP}}]`$** (proved by transfer, given FRAG). Below $`Z^{\mathrm{FP}}`$ every new pair is a $`\tau''`$-$`\delta''`$ pair of level 3
  that contains no new pair, every restart has an exact reach, and there is no fan apex and no triple nest; $`Z^{\mathrm{FP}}`$ is a base point with no $`\le_1`$-predecessor. So $`\beta_0 \gt Z^{\mathrm{FP}}`$,
  $`T_3^C \gt Z^{\mathrm{FP}}`$, $`[0, Z^{\mathrm{FP}}] \subseteq \mathrm{Core}(R_2^C)`$, and $`Z^{\mathrm{FP}}`$ is an InaccPsi normal form with collapse arguments below $`I_\omega`$. The proof is the induction of [SHIFT10.md](SHIFT10.md)
  §2.1 with the corrected values; the skeleton reads only upper bounds (the caps), which the corrected values only lower. This settles the blocking point B-1 of the review there. The frontiers
  on the way are restrictions of it, both halves: $`Z^{\mathrm{LL}}`$, $`L(\theta'_2\cdot\omega^3)`$, $`L(\theta'_2\cdot\Omega_1)`$, $`L(\theta'_2\cdot P')`$ and $`L(\theta'_2\cdot\Omega_2)`$. Corrected values there:
  $`r(Z^{\mathrm{LL}}) = L(\lambda^{\mathrm{LL}}+\omega^2+\omega+1) + L(\lambda^{\mathrm{LL}}+\omega^2)^2`$, and $`r(Z) = L(\theta'_2\cdot\Omega_1 + Z + \omega + 1) + Z`$ for $`Z = L(\theta'_2\cdot\Omega_1)`$. The first code not covered
  is $`\hat G''+G''(\omega^2)`$, at $`Z^{\mathrm{FP}}`$ itself. The $`R_2^S`$ side at $`Z^{\mathrm{FP}}`$ is an outline (not counted).
- **Toward $`\nu_3`$**, by the route that the blocking point B-2 of [SHIFT10.md](SHIFT10.md) §2.1 named. The first hypothesis of SHIFT$`_3`$ is withdrawn and replaced by (H1′): every pair below
  $`\nu_3`$ is skeletal at level 3, and the skeleton of level 3 holds below $`\nu_3`$; it asks for no base point above $`L(\Omega_\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 3)`$.
  - CAP-0″ below $`Z^{\mathrm{FP}}`$ in a sharp form (proved, given FRAG): no restart of level 3 below $`Z^{\mathrm{FP}}`$ crosses itself.
  - LOW-RED″ and BASE″ (proved as implications, without FRAG), and NU-LOW‴ (proved as an implication, given FRAG, once the hypothesis "the right end $`y_3`$ is a restart of level 3" is
    added, m3): from CAP-0″ below $`L(\Omega_\omega)`$, CAP-1″, LONG-CLASS at level 4 and MULTI-FAR one level up, the least pair that is not skeletal at level 3 has its right end at
    least $`\nu_3 = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + \omega^{P_3+1} + P_3)`$. Its clause for $`R_2^C`$ rests on NU-CT$`_3`$, an outline (m4).
  - SHIFT$`_3'`$ (proved as an implication, given FRAG): with (H1′), $`L_3(\omega) \lt_2 L_3(\omega+1)`$ in $`R_2^S`$.
  - **Not proved: $`T_3^S \le \nu_3`$ and $`T_3^S = \nu_3`$** (blocking point B-1 of the review). The triple nest at $`L_3(\omega)`$ uses the block lemma at $`L_3(\omega)`$, which needs a base point or a
    bounded set of $`\le_1`$-predecessors; neither holds, since $`L_3(n) \le_1 L_3(\omega)`$ for every $`n`$. (H1′) does not give that block, and if its clause on crossings is read literally it fails at
    $`L_3(\omega)`$, as the first hypothesis of SHIFT$`_3`$ did.
  - Open: the corrected exact reach for every code below $`P_3`$ at levels 3 and 4 (the first open code is $`\hat G''+G''(\omega^2)`$; up to $`(\hat G'')^2`$ the author expects only checks of
    the domain), then CAP-0″ on $`[Z^{\mathrm{FP}}, L(\Omega_\omega))`$, CAP-1″, LONG-CLASS at level 4, the block at $`L_3(\omega)`$, and NU-CT$`_3`$.
- **Minor point m5**: the reason given for n8 in the paper is not a reason; the bound holds as stated in the paper of §2.1.

### 3.2 $`R_2^S`$ on $`[0, Z^\Lambda)`$, and an induction above $`Z^\Lambda`$ that reads only caps

Words as in §2.2. A crosser of $`b`$ is a point $`x \lt b`$ with $`x \le_1 b`$.

- **The claim in $`R_2^S`$ on $`[0, Z^\Lambda)`$** (proved, given FRAG). From §2.1, $`Z^\Lambda`$ is a base point with no $`\le_1`$-predecessor and $`\beta_0 \gt Z^\Lambda`$; LOC-ISO gives
  $`[0, Z^\Lambda) \subseteq \mathrm{Core}(R_2^S)`$, and Carlson's criterion holds at every pair with right end below $`Z^\Lambda`$. In §2.2 this was conditional.
- **BLOCK″$`_0(Z^\Lambda)`$♯** (proved by transfer, given FRAG): the first block of $`Z^\Lambda`$; its proof never reads $`r(Z^\Lambda)`$. So $`\beta_0 \gt Q^\Lambda`$ and the claim holds in $`R_2^C`$ on
  $`[0, Q^\Lambda]`$ ($`Q^\Lambda`$ as in §2.2; below $`Z^{\mathrm{FP}}`$).
- **The repairs of the review of §2.2** (proved): the labels of B-1; K2$`^{\mathrm{cap}}`$ with one more copy point (m1; given the caps); and **UNIFORM-B⁺**: if $`b`$ is a point $`L(e)`$, the hypotheses of
  UNIFORM-B give $`\beta_0 \gt b`$ and $`T_3^C \gt b`$ (strict); $`b`$ itself may have cofinal $`\le_1`$-predecessors. The referee checked every case of the extra left end.
- **C$`^{\Lambda 1}`$** (proved by transfer, given FRAG): the block lemma holds at $`Z^\Lambda`$ for every block, so $`\beta_0`$ lies above the whole region of $`Z^\Lambda`$.
- **SKEL″$`^{\mathrm{cr}}`$, UPPER$`^{\mathrm{cr}}`$ and PRED1$`^{\mathrm{cr}}`$** (proved by transfer, given FRAG). The skeleton of a region of level 3 holds also when the region is crossed by restarts whose reach
  is not known. The proof runs by induction along the right bound: a crosser $`x`$ with $`x \le_1 \rho`$ gets $`x \le_1 z`$ for the needed $`z`$ from $`x \le_1 \rho \le_1 z`$, so the reach of $`x`$ is never read.
  The referee's main attack (a crosser whose reach ends inside the region and cuts a reach of the skeleton) fails this way; every map used moves points down or stays inside one block. Restarts
  of level 3 with short codes have caps, so the $`\le_1`$-predecessors of each region base lie in the finite set of the long restarts $`Z^\Lambda`$ and $`L(\theta'_2\cdot\omega^2 + G''(\omega^2)\cdot k)`$. Minor points:
  state the induction also at the targets of CROSS-LIM″ and at the base itself (m2); UPPER$`^{\mathrm{cr}}`$ is "given FRAG", not "without FRAG" (m3); name the maps (m4); one finiteness fact (m5);
  one fallback row is a remark (m6).
- **Theorem Z$`^{\mathrm{LG}}`$** (proved by transfer, given FRAG). With $`Z^{\mathrm{LG}} = L(\theta'_2\cdot\omega^2 + \omega^{G''(\omega^2)+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{G''(\omega^2)+1})`$:
  $`\beta_0 \gt Z^{\mathrm{LG}}`$, $`T_3^C \gt Z^{\mathrm{LG}}`$, Carlson's criterion below $`Z^{\mathrm{LG}}`$, and the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{LG}}]`$, with no long reach of level 3. Since
  $`Z^{\mathrm{LG}} \lt Z^{\mathrm{LL}} \lt Z^{\mathrm{FP}}`$, this is a second proof of a part of §3.1, independent of the exact values of level 3.
- **S-COND** (proved as an implication): the claim in $`R_2^S`$ on $`[0, \mu)`$ for every region base $`\mu \le Z^{\mathrm{LG}}`$ that no long restart of level 3 at or above $`Z^\Lambda`$ reaches. Under the
  conjecture LONG″-CAP (a long restart of level 3 of code $`G''(\omega^2)`$ reaches below $`L(\lambda''+\omega^2\cdot 2)`$), the claim in $`R_2^S`$ would hold on $`[0, Z^{\mathrm{LG}})`$ (conditional). Minor point m1:
  for an indecomposable $`\mu`$ with $`r(Z^\Lambda) \lt \mu \le \beta_0`$ the core of $`R_2^S`$ already passes $`Z^\Lambda`$, so a cap $`r(Z^\Lambda) \lt Z^{\mathrm{LG}}`$ alone is enough to pass $`Z^\Lambda`$.
- **Not counted** (no referee has checked it): $`r(Z^\Lambda) = \delta''_1(L(\theta'_2\cdot\omega^2+\omega^2)) + 1`$ ([SHIFT10.md](SHIFT10.md) §1.1, LONG″-$`G''(\omega^2)`$, which stands; also §3.1) is below $`Z^{\mathrm{LG}}`$,
  so with m1 the claim in $`R_2^S`$ would pass $`Z^\Lambda`$.

### 3.3 Lean, stage 4: the restart blocks over ordinal restart indices

- **Files.** Seven new modules of [R2/](R2/) (RstK, Off, BlkX, RSX, OffPhi, OffV, CoreX), and doc lines in Blk3, RS and CitedL (point m3 of the audit of §2.3: the Lean index $`h`$ is the paper's
  $`h - 1`$; `Par_sub` is stated for $`\tau \in E`$ only). In the repository all of them build as modules with the whole library (green, no `sorry`). Details on [LEAN.md](LEAN.md).
- **Lemma TOP$`_\lambda`$** (`RstK.top_gen`, without FRAG): over restart indices that are ordinals, with a restart context that does not ask for caps below $`\rho`$ (they fail at limit indices), for the
  offset terms $`x\cdot m + k`$, with the offset lemma as its input.
- **Lemma RS$`_\lambda`$** (`rs_rst`): FRAG with a restart as target at limit indices, the proof of [REACHES.md](REACHES.md) §1; RS of §2.3 at successor indices.
- **Theorem BLK$`^\Xi`$** (`blkXi`), for every restart index $`\lambda \le \Xi_\omega`$: (i) the $`\lt_2`$-pairs with right end below $`\upsilon_{\Xi_\omega+\omega^2}`$ are exactly the
  $`(\upsilon_{\mu+\omega j}, \upsilon_{\mu+\omega j+1})`$; (ii) $`\rho_\lambda`$ has no $`\lt_1`$-predecessor and no $`\lt_2`$-successor, and $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^*(\lambda)`$; (iii) every point below
  $`\upsilon_{\Xi_\omega+\omega^2}`$ that is not a $`\upsilon`$-point has its reach of $`R_1^+`$. Values: $`\delta + (e-1)`$ at $`\upsilon_{\omega^e}`$ ($`2 \le e \lt \Xi_\omega`$; $`\delta + 2`$ at $`\omega^3`$, $`\delta + \omega`$ at $`\omega^\omega`$),
  $`\delta + \Xi_n`$ at $`\Xi_n`$, $`\delta + \Xi_\omega + 1`$ at $`\Xi_\omega`$.
- **Theorem BLK$`^O`$ below $`V_\omega(1)`$** (`blkV`, `blkPhi`): (i)–(iii) for every restart index below $`V_\omega(1)`$, with the closed form of Theorem OFF-V: the offset is $`c(\lambda)`$ at level 0 and
  $`\rho\cdot n + \mathrm{logend}(\alpha)`$ at $`\lambda = V_n(\alpha)`$; so $`\Phi_1`$ reaches $`\delta + \Phi_1\cdot 2`$. Lean proves the closed form directly, so the recursive offset $`O`$ is not needed below
  $`V_\omega(1)`$ ($`V_0 = \upsilon`$, $`V_{n+1}`$ the derivative of $`V_n`$, $`V_\omega(1) = \sup_n V_{n+1}(1)`$; Lean proves $`\Xi_\omega \lt \Phi_1 \lt V_\omega(1)`$).
- **CORE-C below $`V_\omega(1)`$** (`core_V`): $`[0, V_\omega(1)) \subseteq \mathrm{Core}(R_2^C)`$, without FRAG, from the blocks and Carlson 2009, Thm 14.14 (cited).
- **No new axiom.** The 76 main theorems use 42 of the 44 cited axioms: TOP and the block structure 35 (no fact of FRAG), RS and the block theorems 41, CORE-C 36 (with Thm 14.14).
- **The audit**: every axiom used faithful and none new, every definition right, every main theorem Lean-proved; the cited files unchanged. No fatal and no blocking point. Minor points: (i) is
  about the pairs whose right end is below the bound (n1); (iii) covers the points that are not $`\upsilon`$-points, not the $`\upsilon`$-points that are not restarts (n2); (ii) is stated as the reach,
  and the interval form follows from the interval property `le1_of_le_of_le1`, which uses no axiom (n3). These are written on [LEAN.md](LEAN.md).

### 3.4 Status after the forty-third round

- **Wilken's claim in $`R_2^C`$**: both halves on $`[0, X_4]`$ without FRAG, and **on $`[0, Z^{\mathrm{FP}}]`$ given FRAG** (1 review, §3.1), with $`Z^\Lambda`$ to $`Z^{\mathrm{LG}}`$ by two proofs (2 reviews) and
  $`[0, Z^\Lambda]`$ as in §2.4. Above $`Z^{\mathrm{FP}}`$: not proved.
- **Wilken's claim in $`R_2^S`$**: on $`[0, \upsilon_{\omega^3}]`$ (with or without FRAG), and, given FRAG, on $`[0, Z^\Lambda)`$ (1 review, §3.2). $`\beta_0 \gt Z^{\mathrm{FP}}`$ given FRAG. (E) is open, and $`\beta_0`$ is
  not located.
- **Reaches** (given FRAG): as in §2.4, and at level 3 $`r(b) = k''_b(o_b(c''))`$ for every restart below $`Z^{\mathrm{FP}}`$, long codes included; FALSE-LB″ is proved.
- **LOW: false, given FRAG** (§1.1, 1 review); not touched in this round. $`\nu_3`$: not proved (its upper half has a blocking point).
- **Lean**: as in §2.4, and now TOP$`_\lambda`$, RS$`_\lambda`$, BLK$`^\Xi`$, BLK$`^O`$ and CORE-C below $`V_\omega(1)`$ (§3.3).
- The lower-bound program below $`\theta_0`$: not worked on in this round ($`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$; past $`S_*`$ the conjecture LEX-SELF). The step below SRO: no change (done for every
  $`n`$ on all 3,166 sample matrices; only the general statement for all standard matrices below SRO is open).

### 3.5 Checks of the forty-third round

Each run was under 60 seconds; none is a proof.

- §3.1. Two runs on the terms (normal forms, order and domain of the predicted points at five places: the code $`G''(\omega^2)\cdot 2`$, $`Z^{\mathrm{LL}}`$, $`L(\theta'_2\cdot\Omega_1)`$, and the codes
  $`G''(\omega^2)+\Omega_1`$ and $`\hat G''+\Omega_1`$), 0 failures. The referee ran none: the weak steps are pin and copy arguments, and the ordinal arithmetic was redone by hand.
- §3.2. Eight runs on the terms ($`Q^\Lambda`$, the points of the region of $`Z^\Lambda`$, $`Z^{\mathrm{LG}}`$, and the codes of the long restarts), 0 failures. The referee ran none.
- §3.3. Lean: each of the seven modules alone and all together, green, and a false statement added at the end fails (the audit re-ran them); the repository build of the whole library is
  green, with no `sorry`.

### 3.6 Open

- Above $`Z^{\mathrm{FP}}`$: the exact reach of level 3 for the codes from $`\hat G''+G''(\omega^2)`$ on (the reading past the next $`\psi_{\Omega_2}`$-term above $`\hat G''`$, BOUND♯ and the caps one level up,
  the relative pins, and crossings of long restarts of level 3); then CAP-0″ up to $`L(\Omega_\omega)`$, CAP-1″, LONG-CLASS at level 4, the block at $`L_3(\omega)`$, NU-CT$`_3`$ and $`\nu_3`$.
- The claim above $`Z^{\mathrm{FP}}`$ given FRAG in $`R_2^C`$ (above $`X_4`$ without FRAG), and above $`Z^\Lambda`$ in $`R_2^S`$ (a cap on $`r(Z^\Lambda)`$ below $`Z^{\mathrm{LG}}`$ is enough to pass $`Z^\Lambda`$, §3.2;
  the $`R_2^S`$ side at $`Z^{\mathrm{FP}}`$ is an outline).
- Lean, in order: BLK$`^O`$ above $`V_\omega(1)`$ (offset terms with $`\omega^t`$ and $`\varepsilon_{x+1}`$, which need [W07a] L.4.2 and [W07b] Thm 2.2 in general as cited facts; the proof of Thm 2.2 is in a
  paper we do not have, so its statement would be cited from [W07b] §2, or the project's own proof formalized; or else the recursive offset $`O`$); then SKEL⁺, CAP, LIFT-0, O$`^C`$, NU-CT and $`\nu_C`$;
  the $`R_2^S`$ side.
- $`R_2^S = R_2^C`$: (E), $`\beta_0`$, FAN-LOAD, and the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible (not worked on in this round): past $`S_*`$, capacities with $`\alpha \ge \Gamma_0`$ (conjecture LEX-SELF) or another way; then the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past
  $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; the rest of [COVER.md](COVER.md) §9.
