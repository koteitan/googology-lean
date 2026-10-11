[← Back](README.md) | [English](SHIFT12.md) | [Japanese](SHIFT12-ja.md)

# $`R_2^+`$, the forty-fourth round: the claim in $`R_2^C`$ up to $`Z^{\mathrm{W}}`$ and in $`R_2^S`$ up to $`Z^{\mathrm{FP}}`$, the block at $`L_3(\omega)`$, and the restart blocks of $`R_2^C`$ up to $`\Phi_\Gamma`$ in Lean

This page continues [SHIFT11.md](SHIFT11.md) (§3 there is the forty-third round); §1 is the forty-fourth round. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a fatal or blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known, or of the target, is not counted as progress.

## 1. The forty-fourth round

Three papers (2026-10): the exact reaches of level 3 past $`Z^{\mathrm{FP}}`$ with the block at $`L_3(\omega)`$ (§1.1) and the $`R_2^S`$ side past $`Z^\Lambda`$ (§1.2), each refereed once, and the fifth Lean
stage for $`R_2^C`$ (§1.3), whose audit checked the axioms and the definitions (Lean checks the proofs). A result in this section has 1 review unless a count is given. Levels are numbered as in
[SHIFT11.md](SHIFT11.md) §1 (one higher than in the papers): the restarts $`L(\lambda'')`$ are at level 3, and the points $`L_3(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + P_3\cdot e)`$ are the restarts of level 4.

**The frontier in $`R_2^C`$ moves to $`Z^{\mathrm{W}}`$.** Given FRAG, **Wilken's claim holds in $`R_2^C`$ on $`[0, Z^{\mathrm{W}}]`$, both halves**, with

```math
Z^{\mathrm{W}} = L(\theta'_2\cdot(\Omega_2+\omega^2)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\theta'_2+2}),\qquad \theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2),
```

and $`\beta_0 \gt Z^{\mathrm{W}}`$ and $`T_3^C \gt Z^{\mathrm{W}}`$ (1 review, §1.1). The name says that the codes below $`Z^{\mathrm{W}}`$ are read inside one window of the restart (defined in §1.1). On the way:
$`L(\theta'_2\cdot(\Omega_2+1)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \theta'_2)`$. The step from $`Z^{\mathrm{FP}}`$ to

```math
Z^{\mathrm{FPG}} = L(\theta'_2\cdot\Omega_2 + \omega^{\hat G''+G''(\omega^2)} + \omega^{G''(\omega^2)+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\hat G''+G''(\omega^2)} + \omega^{G''(\omega^2)+1})
```

has a second proof that reads only caps (§1.2), so it has **2 reviews**. **In $`R_2^S`$ the claim now holds on $`[0, Z^{\mathrm{FP}})`$**, given FRAG (1 review, §1.2), and on the way the reach of $`Z^\Lambda`$
is known. Toward $`\nu_3`$: the blocking point of the forty-third round (the block at $`L_3(\omega)`$) is closed, and $`T_3^S = \nu_3`$ now follows from three named hypotheses; $`\nu_3`$ itself is
not proved.

Papers cited: in §1.1 and §1.2 only through refereed stages: [W07b] (L.2.1), Carlson 2009 (Def 5.3, L.5.5, L.5.7 (3)), Wilken 2020 ((21.10), (21.12), Prop 21.6, Prop 21.11, Thm 21.13),
[CW12b] (L.7.5), and in §1.2 also [C11] (through LOC-ISO). In §1.3: [W07a] (Def 3.22, Def 3.28, L.3.30, L.4.2, Def 5.1) and [W07b] (Thm 2.2, cited from its statement), with the facts already cited in
Lean. None uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006).

The minor points of the reviews of the forty-third round are applied: m1–m7 of the review of [SHIFT11.md](SHIFT11.md) §3.1 in the paper of §1.1 (m1 as a far top lemma with a larger finite set of
pins, proved by transfer), m1–m6 of the review of §3.2 there in the paper of §1.2, and n1–n3 of the audit of §3.3 there in the Lean doc lines (§1.3).

### 1.1 The exact reach of level 3 up to $`Z^{\mathrm{W}}`$, the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{W}}]`$, and the block at $`L_3(\omega)`$

Notation as in [SHIFT11.md](SHIFT11.md) §3.1: for a restart $`b = L(\lambda'')`$ of level 3, $`F''_b = L(\lambda''+\Omega_1)`$, $`o_b`$ is the reading at $`b`$, $`k''_b`$ enumerates the points that are closed
relative to $`b`$, $`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$ and $`\hat G'' = G''(\Omega_2)`$. **The window** of $`b`$ is $`[b, L(\lambda''+\Omega_1+\omega^2))`$; the far pins of
[SHIFT10.md](SHIFT10.md) §2.1 live there.

- **TIER and THETA″$`^W`$** (proved, without FRAG). For $`x \lt \omega^2`$ the tier map carries the codes of level 1 in $`[\Omega_1, P')`$ onto the codes in $`[G''(\Omega_2+x), G''(\Omega_2+x+1))`$; its step does not
  read the tier, since $`\Omega_2+x`$ has no collapse. The reading is $`o_b(G''(\Omega_2+x)) = L(\lambda''+\Omega_1+x)`$, so $`o_b`$ maps the codes below $`G''(\Omega_2+\omega^2)`$ onto $`[0, L(\lambda''+\Omega_1+\omega^2))`$; the codes
  below $`\Omega_1`$ are read below $`b`$, the others inside the window. Also the range lemmas up to the index of $`Z^{\mathrm{W}}`$: **below $`Z^{\mathrm{W}}`$ no long restart of level 3 is crossed** (every
  restart crossed is short or is $`F''_b`$). Minor: one sentence says that every code is read inside the window, which is false below $`\Omega_1`$, and the limit step should name the continuity fact it
  uses (m1).
- **Theorem ENUM-REACH″$`^{\mathrm{W}}`$** (proved by transfer, given FRAG). For every restart $`b = L(\lambda'')`$ of level 3 below $`Z^{\mathrm{W}}`$, with code $`c''`$: $`r(b) = k''_b(o_b(c''))`$, both halves. A code
  $`c'' \ge \hat G''`$ lands at $`F''_b`$, and $`r(b) = k''_{F''_b}(o_b(c'')) \lt L(\lambda''+\Omega_1+\omega^2)`$. For example, the π-code $`G''(\Omega_2+\omega+1)`$ gives $`r(b) = \delta''_1(F''_b)\cdot 2`$. The "$`\ge`$" half is the long
  restart step on the window; the "$`\le`$" half is the far top lemma with the larger set of pins. Also the order of the values, $`r(b) \ge o_b(c'')`$, the sharp crossing rule, and the cap. The referee
  recomputed the examples by hand. Minor: one condition of the far top lemma (the finite set reaches the right block) holds but is not written (m2).
- **Theorem C$`^{\mathrm{W}\sharp}`$ and the claim on $`[0, Z^{\mathrm{W}}]`$** (proved by transfer, given FRAG). Below $`Z^{\mathrm{W}}`$ every new pair is a $`\tau''`$-$`\delta''`$ pair of level 3 that contains no
  new pair, every restart has an exact reach, and there is no fan apex and no triple nest; $`Z^{\mathrm{W}}`$ and every $`L(\theta'_2\cdot(\Omega_2+x))`$, $`1 \le x \le \omega^2`$, is a point with no $`\le_1`$-predecessor
  that nothing below reaches past. So $`\beta_0 \gt Z^{\mathrm{W}}`$, $`T_3^C \gt Z^{\mathrm{W}}`$, $`[0, Z^{\mathrm{W}}] \subseteq \mathrm{Core}(R_2^C)`$, and $`Z^{\mathrm{W}}`$ is an InaccPsi normal form with collapse arguments
  below $`I_\omega`$. The points $`L(\theta'_2\cdot(\Omega_2+x))`$ on the way are restrictions, both halves. The first code not covered is $`G''(\Omega_2+\omega^2)`$, the π-code of $`Z^{\mathrm{W}}`$ itself, whose
  reading leaves the window. The referee recomputed the formula of $`Z^{\mathrm{W}}`$. Minor: the atoms of a crosser whose reach ends inside the region of $`F''_b`$ are covered by the two cases of
  BASE-INV, not by "true on both sides" (m3). The $`R_2^S`$ side at $`Z^{\mathrm{W}}`$ is an outline (not counted).
- **CAP-0″ below $`Z^{\mathrm{W}}`$**, sharp form (proved, given FRAG): no restart of level 3 below $`Z^{\mathrm{W}}`$ crosses itself.
- **Toward $`\nu_3 = L_3(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + \omega^{P_3+1} + P_3)`$.** Let $`y_3`$ be the least right end of a pair of $`R_2^S`$ that is not skeletal at level 3.
  - **TAUL** (proved, without FRAG): no restart of level 3 is the left end of a skeletal pair of level 3. Minor: the proof should say that every skeletal left end of the lower levels is below
    $`L(0)`$ or strictly inside a gap $`(L(e), L(e+1))`$ (m5).
  - **SKEL″$`^\nu`$** (proved by transfer, given FRAG, in $`R_2^S`$ below $`\min(y_3, L(\Omega_\omega))`$; above $`L(\Omega_\omega)`$ proved as an implication): the skeleton of a region of level 3 holds below
    $`y_3`$ **whatever its $`\le_1`$-predecessors are**, also when they are cofinal in it. A crosser is a restart of level 3, so by TAUL and the choice of $`y_3`$ its $`\lt_2`$-atoms are false in both
    structures, and its $`\le_1`$-atoms are handled for one finite set at a time, as for SKEL⁺ one level down ([BREAK.md](BREAK.md) §2). No base point is needed. Minor: name the earlier lemma
    that this generalizes, read "the base is not a left end" as "the base has no $`\lt_2`$-successor below $`y_3`$" (it is the left end of $`L_3(\omega) \lt_2 \nu_3`$), and label it an $`R_2^S`$ statement (m4).
  - **SHIFT$`_3''`$** (proved as an implication, given FRAG). From (Y) $`y_3 \ge \nu_3`$, (H2$`^{\mathrm{cr}}`$) the exact reaches of the restarts that cross $`L_3(\omega)`$, and (H3) FRAG and the gap calculus
    above $`L(\Omega_\omega)`$: $`L_3(\omega) \lt_2 \nu_3`$ in $`R_2^S`$, the block of $`L_3(\omega)`$ (from SKEL″$`^\nu`$) contains a pair of level 3 with a pair of level 2 inside, so there is a triple nest
    below $`\nu_3`$ and $`T_3^S = y_3 = \nu_3`$. **This closes the blocking point B-1 of [SHIFT11.md](SHIFT11.md) §3.1**: the block at $`L_3(\omega)`$ no longer asks for a base point or a bounded set of
    $`\le_1`$-predecessors. The referee recomputed the triple nest and the name of $`\nu_3`$. Minor: (Y) rests on inputs that are open, so "$`T_3^S = \nu_3`$" stays an implication (m6).
  - NU-LOW‴ with the hypotheses of the forty-third review (proved as an implication): it gives (Y) in $`R_2^S`$; its clause for $`R_2^C`$ rests on NU-CT$`_3`$ (an outline).
  - **Not proved: $`\nu_3`$.** Open inputs: CAP-0″ on $`[Z^{\mathrm{W}}, L(\Omega_\omega))`$, CAP-1″, LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$), and LEFT⁺ one level up (one named step, which would give
    the two hypotheses on left ends of NU-LOW‴). Outlines: (H3) and NU-CT$`_3`$.
- **Past $`Z^{\mathrm{W}}`$** (not counted): the second window (far pins over the offsets $`\Omega_1+x'`$) is an outline, with the predicted next frontier $`L(\theta'_2\cdot\Omega_2\cdot 2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2}\cdot 2)`$;
  the first crossing of a long restart of level 3, at the code $`G''(\theta'_3\cdot\omega^2)`$ with $`\theta'_3 = \psi_{\Omega_4}(\Omega_\omega\cdot 2)`$, is a conjecture.

### 1.2 $`R_2^S`$ on $`[0, Z^{\mathrm{FP}})`$, and the induction with caps only at $`Z^{\mathrm{FP}}`$

Words as in [SHIFT11.md](SHIFT11.md) §3.2. A crosser of $`b`$ is a point $`x \lt b`$ with $`x \le_1 b`$.

- **The reach of $`Z^\Lambda`$ and LONG″-CAP** (proved, given FRAG). As an instance of ENUM-REACH″$`^{\mathrm{FP}}`$ ([SHIFT11.md](SHIFT11.md) §3.1) at the π-code $`G''(\omega^2)`$:

  $`r(Z^\Lambda) = \delta''_1(L(\theta'_2\cdot\omega^2+\omega^2)) + 1 = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{P'+2} + \omega^{P'+1} + P') + 1,`$

  and every restart $`b = L(\lambda'')`$ of level 3 below $`Z^{\mathrm{FP}}`$ whose code or π-code is $`G''(\omega^2)`$ has $`r(b) = \delta''_1(L(\lambda''+\omega^2)) + 1 \lt L(\lambda''+\omega^2\cdot 2)`$. This is the conjecture
  LONG″-CAP of [SHIFT11.md](SHIFT11.md) §3.2, with the conjectured value. The review of §3.1 there checked the codes; for the π-code the value has a second refereed source, LONG″-$`G''(\omega^2)`$ of
  [SHIFT10.md](SHIFT10.md) §1.1, which stands (the withdrawn results do not reach it). Minor: cite that source inside the proof (m4).
- **LOC-PASS** (proved). If $`Z \lt \beta_0`$ is a point with no $`\le_1`$-predecessor that nothing below reaches past, and an indecomposable $`\mu`$ lies in $`(r(Z), \beta_0]`$, then the core of $`R_2^S`$
  contains $`[0, Z]`$ (by LOC-ISO). This is m1 of the review of §3.2 there.
- **S-PAST-Λ** (proved, given FRAG). Every base $`\mu`$ of a region of level 3 in $`(Z^\Lambda, Z^{\mathrm{LG}}]`$ has no $`\le_1`$-predecessor unless $`\mu`$ is the next restart point after one long restart of
  code $`G''(\omega^2)`$ below it; so the claim holds in $`R_2^S`$ on $`[0, Z^{\mathrm{LG}})`$. Minor: the paper's first lines say "by the cap of $`r(Z^\Lambda)`$ alone"; the proof needs LONG″-CAP at every
  $`L(\theta'_2\cdot\omega^2 + G''(\omega^2)\cdot k)`$, and $`r(Z^\Lambda)`$ alone gives only $`[0, L(\theta'_2\cdot\omega^2 + G''(\omega^2)))`$ (m1).
- **S-FOLLOW and the claim in $`R_2^S`$ on $`[0, Z^{\mathrm{FP}})`$** (proved, given FRAG). If $`Z`$ is a $`\upsilon`$-point with $`\beta_0 \gt Z`$ and no $`\le_1`$-predecessor in $`R_2^S`$, the claim holds in $`R_2^S`$
  on $`[0, Z)`$. So every frontier of $`R_2^C`$ of this form gives the same frontier in $`R_2^S`$ (half open). With [SHIFT11.md](SHIFT11.md) §3.1: **the claim holds in $`R_2^S`$ on $`[0, Z^{\mathrm{FP}})`$**, and
  Carlson's criterion holds at every pair of $`R_2^S`$ below $`Z^{\mathrm{FP}}`$. Minor: the weakest step named in the paper is not weak (below $`\beta_0`$ the two structures agree); the real dependency is
  [SHIFT11.md](SHIFT11.md) §3.1 as a whole, with 1 review (m3); a remark says "if and only if" where only "if" is proved (m2).
- **The induction with caps only, at the base $`Z^{\mathrm{FP}}`$** (proved by transfer, given FRAG). The induction of [SHIFT11.md](SHIFT11.md) §3.2 reads its base point only through three properties
  ($`\beta_0`$ is above it, nothing below reaches past it, and the gap calculus holds in every gap below it), which $`Z^{\mathrm{FP}}`$ has. Run at $`Z^{\mathrm{FP}}`$: $`\beta_0 \gt Z^{\mathrm{FPG}}`$, $`T_3^C \gt Z^{\mathrm{FPG}}`$,
  Carlson's criterion below $`Z^{\mathrm{FPG}}`$, and the claim in $`R_2^C`$ on $`[0, Z^{\mathrm{FPG}}]`$. The referee looked for a property of $`Z^\Lambda`$ that the proof reads and $`Z^{\mathrm{FP}}`$ lacks; seven
  candidates all transfer. Since $`Z^{\mathrm{FP}} \lt Z^{\mathrm{FPG}} \lt L(\theta'_2\cdot(\Omega_2+1)) \lt Z^{\mathrm{W}}`$, this is a second proof of $`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$, independent of the exact values of §1.1.
- **S-COND$`^{\mathrm{FP}}`$** (proved as an implication): the claim in $`R_2^S`$ on $`[0, \mu)`$ for each region base $`\mu \le Z^{\mathrm{FPG}}`$ above $`Z^{\mathrm{FP}}`$ that no long restart of code $`G''(\omega^2)`$ at or above
  $`Z^{\mathrm{FP}}`$ reaches. A cap on $`r(Z^{\mathrm{FP}})`$ (conjecture CAP$`^{\mathrm{FP}}`$) would take $`R_2^S`$ past $`Z^{\mathrm{FP}}`$.

### 1.3 Lean, stage 5: the restart blocks up to $`\Lambda_\Gamma`$ and below $`\Phi_\Gamma`$

- **Files.** Eight new modules of [R2/](R2/) (CitedW, FragX, Exact, RSG, TopG, BlkG, OffG, OffG2), and doc lines in RSX, OffPhi, OffV and BlkX (points n1–n3 of the audit of
  [SHIFT11.md](SHIFT11.md) §3.3; the code is unchanged). In the repository all of them build as modules with the whole library (green, no `sorry`). Details on [LEAN.md](LEAN.md).
- **Five new cited axioms** (file CitedW): [W07b] Thm 2.2, cited from its statement ($`\alpha \le_1 \alpha+\xi`$ in $`R_1`$ for $`0 \lt \xi \le \alpha`$ iff $`\alpha = \omega^{\alpha'}`$ with $`\mathrm{logend}(\alpha') \ge \xi`$;
  its proof is in a paper that is not used); [W07a] L.4.2 ($`\vartheta^\tau(1+\alpha) = \bar\omega_{\tau+\alpha}`$, $`\bar\omega`$ the enumeration of the additive principal numbers that are not $`\varepsilon`$-numbers);
  [W07a] Def 3.22, Def 3.28 and L.3.30 ($`\vartheta^\tau(\xi)`$ is a term with the parameters of $`\xi`$); [W07a] Def 5.1, fourth clause (the base change of a $`\vartheta^\tau`$-term); and the constant
  $`\vartheta^\tau`$. As in the earlier stages, $`\Omega_1`$ of [W07a] is taken to be $`\omega_1`$.
- **FRAG with the base change on $`D_1`$** (`fragX`): on the points of $`D_1`$ the map of FRAG is the single base change $`\pi`$. No new axiom.
- **Lemma EXACT** (`pi_tq`): $`\pi(r\cdot\gamma+e) = s\cdot\gamma+e`$ and $`\pi(r\cdot r+e) = s\cdot s+e`$ for the base change $`\pi`$ from $`r`$ to $`s`$ ($`\gamma, e \lt s`$).
- **RS with a restart target** for these terms (`rs_rstG`), **Lemma IMG** (`wit_pow`, `wit_mul`, `wit_sq`: a copy does not make these terms smaller) and **TOP$`^O`$** (`top_tq`, without FRAG).
- **Theorem BLK$`^O`$ up to $`\Lambda_\Gamma`$** (`blkG`): (i)–(iii) of BLK$`^O`$ for every restart index $`\lambda \le \Lambda_\Gamma`$, with the closed form of OFF-V at **every ordinal level**: the offset is $`c(\lambda)`$
  at level 0, $`\rho\cdot\gamma + \mathrm{logend}(\alpha)`$ at $`\lambda = V_\gamma(\alpha)`$ for any $`\gamma \ge 1`$, and $`\rho\cdot\rho`$ at $`\Lambda_\Gamma`$. Values: $`\mathrm{lh}(V_\omega(1)) = \delta + V_\omega(1)\cdot\omega`$ and
  $`\mathrm{lh}(\Lambda_\Gamma) = \delta + \Lambda_\Gamma^2`$.
- **Theorem BLK$`^O`$ below $`\Phi_\Gamma`$** (`blkG2`). $`\Phi_\Gamma`$ is the first fixed point of the enumeration $`G_\Gamma`$ of the Γ-points ($`G_\Gamma(1) = \Lambda_\Gamma`$; a Γ-point is a $`\lambda \gt 0`$ with
  $`V_\gamma(\lambda) = \lambda`$ for all $`\gamma \lt \lambda`$). At a Γ-point $`G_\Gamma(\alpha)`$ the offset is $`\rho^2 + \mathrm{logend}(\alpha)`$; at the other restart indices it is that of OFF-V. Lean proves
  $`V_\omega(1) \lt \Lambda_\Gamma \lt \Phi_\Gamma \lt \Omega_1`$.
- **CORE-C** (`coreG2`): $`[0, \Phi_\Gamma) \subseteq \mathrm{Core}(R_2^C)`$, without FRAG (before: $`[0, V_\omega(1))`$).
- **Axioms.** The main theorems use 47 of the 49 cited axioms (the 42 of stage 4 and the 5 new ones); the cited axioms are now 49 in five files (10 constants and 39 facts).
- **The audit**: the five new axioms faithful, every definition right (the Γ-points and $`\Lambda_\Gamma`$ are the sets of [REACHES.md](REACHES.md) §1 and [PINS.md](PINS.md)), every main theorem Lean-proved; it
  printed the axioms of all 160 theorems of the stage. No fatal and no blocking point. Minor: the counts of the axioms on [LEAN.md](LEAN.md) (m1); say there that [W07b] Thm 2.2 is cited from its statement only (m2)
  and that $`\Omega_1 = \omega_1`$ (m3); the offset $`\rho^2+\rho`$ expected at $`\Phi_\Gamma`$ is on paper only and is not a Lean result (m4); the range below $`\Phi_\Gamma`$ contains the range up to $`\Lambda_\Gamma`$ (m5).

### 1.4 Status after the forty-fourth round

- **Wilken's claim in $`R_2^C`$**: both halves on $`[0, X_4]`$ without FRAG, and **on $`[0, Z^{\mathrm{W}}]`$ given FRAG** (1 review, §1.1), with $`(Z^\Lambda, Z^{\mathrm{LG}}]`$ and $`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$ by
  two proofs (2 reviews). Above $`Z^{\mathrm{W}}`$: not proved.
- **Wilken's claim in $`R_2^S`$**: on $`[0, \upsilon_{\omega^3}]`$ (with or without FRAG), and, given FRAG, **on $`[0, Z^{\mathrm{FP}})`$** (1 review, §1.2). $`\beta_0 \gt Z^{\mathrm{W}}`$ given FRAG. (E) is open, and
  $`\beta_0`$ is not located.
- **Reaches** (given FRAG): at level 3 $`r(b) = k''_b(o_b(c''))`$ for every restart below $`Z^{\mathrm{W}}`$; $`r(Z^\Lambda)`$ as in §1.2.
- **LOW: false, given FRAG** ([SHIFT11.md](SHIFT11.md) §1.1, 1 review); not touched in this round. **$`\nu_3`$: not proved**; its upper half is now an implication from three named hypotheses (§1.1).
- **Lean**: as in [SHIFT11.md](SHIFT11.md) §3.4, and now BLK$`^O`$ up to $`\Lambda_\Gamma`$ and below $`\Phi_\Gamma`$, with CORE-C below $`\Phi_\Gamma`$ (§1.3).
- The lower-bound program below $`\theta_0`$: not worked on in this round ($`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$; past $`S_*`$ the conjecture LEX-SELF). The step below SRO: no change (done for every
  $`n`$ on all 3,166 sample matrices; only the general statement for all standard matrices below SRO is open).

### 1.5 Checks of the forty-fourth round

Each run was under 60 seconds; none is a proof.

- §1.1. The author: names, tiers, codes and readings (normal forms, order and domain of the predicted points), and the tier map forwards and backwards on four tiers, 0 failures; in the first run
  one test condition was wrong (it treated some long codes as failures) and was corrected, and the record says so. The referee: 375 random restart indices of level 3 (codes and windows) and the
  tier map on two more tiers, 0 failures; the referee's first run used an offset that is not a normal form, and only the second run counts.
- §1.2. The author: three runs on the terms (normal forms, domain, order), 0 failures. The referee: 600 cases comparing the domain, the class of the code and the order at the two bases $`Z^\Lambda`$
  and $`Z^{\mathrm{FP}}`$, 0 mismatches.
- §1.3. Lean: each of the eight modules alone and all together, green, and a false statement added at the end fails (the audit re-ran them); the repository build of the whole library is green,
  with no `sorry`.

### 1.6 Open

- Above $`Z^{\mathrm{W}}`$: the second window (the far pins over the offsets $`\Omega_1+x'`$, the readings of the tiers past $`\Omega_2+\omega^2`$), then the crossings of long restarts of level 3 from the code
  $`G''(\theta'_3\cdot\omega^2)`$ on (the counting of [SHIFT11.md](SHIFT11.md) §1.1 one level up); then CAP-0″ up to $`L(\Omega_\omega)`$, CAP-1″, LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$), LEFT⁺ one level up, (H3),
  NU-CT$`_3`$ and $`\nu_3`$.
- The claim above $`Z^{\mathrm{W}}`$ given FRAG in $`R_2^C`$ (above $`X_4`$ without FRAG), and above $`Z^{\mathrm{FP}}`$ in $`R_2^S`$ (a cap on $`r(Z^{\mathrm{FP}})`$, conjecture CAP$`^{\mathrm{FP}}`$; the $`R_2^S`$ side at
  $`Z^{\mathrm{W}}`$ is an outline).
- Lean, in order: BLK$`^O`$ from $`\Phi_\Gamma`$ to $`\Lambda_\varepsilon`$ (offset terms in general Cantor normal form, or more closed-form layers); the recursive offset $`O`$; then SKEL⁺ and CAP (the block
  induction in Lean still needs the exact reach of each restart; the next step is a form that does not compute reaches), LIFT-0, O$`^C`$, NU-CT and $`\nu_C`$; the $`R_2^S`$ side.
- $`R_2^S = R_2^C`$: (E), $`\beta_0`$, FAN-LOAD, and the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible (not worked on in this round): past $`S_*`$, capacities with $`\alpha \ge \Gamma_0`$ (conjecture LEX-SELF) or another way; then the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past
  $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; the rest of [COVER.md](COVER.md) §9.
