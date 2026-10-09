[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/PoR/InaccPsi: Wilken's claim on the core of $`R_2^+`$

Patterns of resemblance → terms of [InaccPsi](../../../Notation/InaccPsi/README.md) (Buchholz's
$`\psi`$ over $`\omega`$ weakly inaccessible cardinals). This directory records the work on a claim of
G. Wilken: what the claim says, what is proved, what is open, and the experiments.

Status words: **Lean** (checked by Lean, no `sorry`, only the axioms `propext`, `Classical.choice`,
`Quot.sound`); **proved** (on paper, and an independent referee found it proved with no fatal or
blocking point; "(2026-10, 2 reviews)" means the result is from October 2026 and two independent referees
checked it; a proved result with no count had 1 review); **cited** (a paper and the place); **checked** (computed on finitely many cases);
**conjecture**; **open**.

## 1. The claim and its source

G. Wilken, "A glimpse of Σ₃-elementarity" (2020), pp. 420–421, repeated in G. Wilken, "Pure
Σ₂-elementarity beyond the core" (APAL 172, 2021), §1:

> We claim that the segment of countable ordinals denoted by the Skolem-hull notation system
> derived from the first ω-many weakly inaccessible cardinals covers (the domain of) Core(R2+).

Here $`R_2^+ = (\mathrm{Ord}; 0, +, \le, \le_1, \le_2)`$, and the core is the union of the least
(isominimal) realizations of its finite patterns. Wilken adds that the system for one weakly
inaccessible cardinal matches the ordinal of the set theory KPI, and that the analysis of $`R_2^+`$
is future work which needs the arithmetic begun in Weiermann–Wilken, "Ordinal arithmetic with
simultaneously defined θ-functions" (MLQ 57, 2011). On p. 438 of the 2020 paper he says that the
core of $`R_2^+`$ "will be shown" to be an initial segment. No definition of the notation system and
no proof is in the papers we have.

## 2. Our precise statement

This section is our reading of the claim. It has no referee; it fixes three choices.

**(a) What "covers" means.** In the same paragraph Wilken says that the cores of $`R_1^+`$ and
$`R_2`$ "cover the same initial segment", that is, they are that segment. So the strongest reading is
equality of sets, $`\mathrm{Core}(R_2^+) = \rho`$, where $`\rho`$ is the set of countable values of the
notation system. The two halves are the upper bound $`\mathrm{Core}(R_2^+) \subseteq \rho`$ and the lower
bound $`\rho \subseteq \mathrm{Core}(R_2^+)`$.

**(b) Which $`R_2^+`$.** Wilken defines $`\le_i`$ by $`\Sigma_i`$-elementarity; we write $`R_2^S`$.
Carlson, "Patterns of resemblance of order 2" (APAL 158, 2009), Defs 5.3–5.4, defines it by coverings;
we write $`R_2^C`$. They are proved equal only below $`\upsilon_{\omega\cdot\omega}`$ (Theorem EQB in
[R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md)), far below every candidate for $`\rho`$. We take $`R_2^C`$
first, because its core is known to be an initial segment: by Carlson 2009, Thm 14.14, it is the least
$`\kappa`$ with $`\kappa \le_1 \beta`$ for all $`\beta \ge \kappa`$. Then the claim reads
$`\rho \le_1 \beta`$ for all $`\beta \ge \rho`$ (upper bound) and no smaller ordinal has this property
(lower bound). $`R_2^S`$ comes second.

**(c) Which notation system.** What matters is the bound $`X`$ on the arguments of the collapses.
Write $`\rho_X`$ for the countable values of the InaccPsi terms whose collapse arguments are all below
$`X`$. Three candidates:

| reading | bound | countable part |
|---|---|---|
| A (first choice) | $`I_\omega`$ | $`\rho_A = \psi_{\Omega_1}(I_\omega)`$ |
| B | $`\varepsilon_{I_\omega+1}`$ | $`\rho_B = \psi_{\Omega_1}(\varepsilon_{I_\omega+1})`$ |
| S (the whole system) | none | $`\rho_S = \psi_{\Omega_1}(\Lambda)`$, $`\Lambda`$ the least $`\alpha \gt I_\omega`$ with $`\Omega_\alpha = \alpha`$ |

Lean proves $`\rho_A \lt \rho_B \lt \rho_S`$, so at most one reading can hold with equality. We take
A first: Wilken's own systems $`T^\tau`$ are unions of systems of finite level, and the countable part
of such a union is the collapse of the supremum. Also
$`\sup_k \psi_{\Omega_1}(I_k) = \sup_k \psi_{\Omega_1}(\varepsilon_{I_k+1}) = \psi_{\Omega_1}(I_\omega)`$
(continuity, Lemma CONT below), so A fits the remark on KPI too. That other standard systems give the same
countable ordinal at the same bound is a conjecture.

So the main statement is, in $`R_2^C`$ and reading A:

```math
\mathrm{Core}(R_2^C) = \psi_{\Omega_1}(I_\omega) = \{\, |t| : t \text{ an InaccPsi normal form, all collapse arguments } \lt I_\omega,\ |t| \lt \Omega_1 \,\}.
```

Both halves are **open**. Below $`\upsilon_{\omega\cdot\omega}`$ both hold, and in $`R_2^C`$ also up to
$`\Phi_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$, with $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$, the first fixed point of $`\alpha \mapsto \Xi_\alpha`$, where $`\Xi_\alpha`$ is the
$`\alpha`$-th fixed point of $`\iota \mapsto \upsilon_\iota`$ (§3, [RESTARTS.md](RESTARTS.md) and [REACHES.md](REACHES.md)), then up to
$`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$ ([PINS.md](PINS.md) §3), then up to $`\rho_{\Lambda'+\omega^2}`$ ([FANFREE.md](FANFREE.md) §10.4),
$`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$ and $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ ([VEBLEN.md](VEBLEN.md) §1, §8), then up to

```math
\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)
```

(2 reviews; [THETA.md](THETA.md) §1, §9.1), then up to $`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ with $`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$
(2 reviews; $`X_2 = \nu_P`$, 1 review), then up to $`X_3 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$ (1 review, [THETA.md](THETA.md) §9.1),
then up to

```math
X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2),\quad G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})
```

(1 review, no FRAG, [SHIFT.md](SHIFT.md) §1), and, given FRAG, up to $`X_5`$ ([SHIFT.md](SHIFT.md) §8.1), up to $`X_8`$ (2 reviews, [SHIFT.md](SHIFT.md) §9.1), up to $`X_9 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_1} + \omega^{G(\Omega_1)+1} + \omega^{G_2+1})`$ with $`G(\Omega_1) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_1})`$
(2 reviews, [SHIFT2.md](SHIFT2.md) §1.1, §2.1), then, past the first index fixed point, up to $`X_{11}`$ ([SHIFT2.md](SHIFT2.md) §2.1), up to $`X_{12}`$ ([SHIFT2.md](SHIFT2.md) §3.1), up to $`X_{13}`$ ([SHIFT3.md](SHIFT3.md) §1.1), up to $`X_{14}`$ ([SHIFT3.md](SHIFT3.md) §2.1), up to $`X_{15}`$ and $`X_{16}`$ (2 reviews, [SHIFT4.md](SHIFT4.md) §1.1, §1.4, §2.1), up to $`X_{17}`$ ([SHIFT4.md](SHIFT4.md) §2.1), up to $`X_{18}`$ (2 reviews; [SHIFT4.md](SHIFT4.md) §2.2, [SHIFT5.md](SHIFT5.md) §1.1), up to $`X_{19}`$ ([SHIFT5.md](SHIFT5.md) §1.1), up to $`X_{21} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_H + \omega^{G(\hat\zeta_H)+1}\cdot 2)`$ with $`\hat\zeta_H = \theta_3\cdot\Omega_3 + \omega^{\hat g_3+g_3}`$
(2 reviews; [SHIFT5.md](SHIFT5.md) §2.1, [SHIFT6.md](SHIFT6.md) §1.1), up to $`X_{22}`$ ([SHIFT6.md](SHIFT6.md) §1.1), and up to

```math
X_{23} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_{23} + \omega^{G(\hat\zeta_{23})+1}\cdot 2),\quad \hat\zeta_{23} = \theta_4\cdot\Omega_4 + \varepsilon_{\hat g_4+1}
```

([SHIFT6.md](SHIFT6.md) §2.1, §3.1; $`X_{22}`$ and $`X_{23}`$ were not proved as written until the blocking point B-1 in the exact long reaches that their cushion caps use was repaired, with 1 review
of the repair, [SHIFT6.md](SHIFT6.md) §3.1; $`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$, $`\theta_4 = \psi_{\Omega_5}(\Omega_\omega)`$, and $`g_3`$, $`\hat g_3`$, $`\hat g_4`$ and the other multipliers with a hat used below are defined in
[SHIFT5.md](SHIFT5.md) and [SHIFT6.md](SHIFT6.md)). Then, given FRAG, the claim holds up to

```math
L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P'),\quad P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)
```

(1 review, [SHIFT7.md](SHIFT7.md) §1.1). This is the conjectured name of the first non-skeletal point $`\nu`$, far above $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, so the hypothesis LOW
($`\nu_C \le \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$) is false given FRAG. The core half alone is proved in $`R_2^C`$ further, on
$`[0, \nu_C]`$, where $`\nu_C`$ ($`\ge L(\omega+1)`$ given FRAG, $`\ge X_4`$ without it) is the first point where $`R_2^C`$ stops being skeletal ([BREAK.md](BREAK.md) §2).

## 3. What is proved

**Summary.** Below $`\upsilon_{\omega\cdot\omega}`$ the claim holds, in both $`R_2^C`$ and $`R_2^S`$: every ordinal
below $`\upsilon_{\omega\cdot\omega}`$ is in the core, and it is the countable value of an InaccPsi normal form whose
collapse arguments are below $`I_\omega`$ (Theorem LOW below). Wilken's points have exact names:
$`\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ for $`\eta \lt \Gamma_0`$ (Theorem T, §4), later for every $`\upsilon`$-point below
$`\upsilon^*`$ (Theorem GEN), for $`\eta \lt \Omega_\omega`$ (GEN⁺, a case of GEN-EXT), and now for every $`\eta`$ in a class that reaches past $`I_\omega`$ (GEN-ALL, [SHIFT5.md](SHIFT5.md) §1.3). In $`R_2^C`$ the claim holds up to $`X_4`$, and up to $`L(\omega+1)`$ given FRAG, and the core contains
$`[0, \nu_C]`$ (§2). The work came in rounds of four refereed papers. This page has the results of the first round (some are on [ROUND1.md](ROUND1.md)); the later rounds are on the pages
[RESTARTS.md](RESTARTS.md), [REACHES.md](REACHES.md), [PINS.md](PINS.md), [BREAK.md](BREAK.md), [COVER.md](COVER.md), [FANFREE.md](FANFREE.md), [VEBLEN.md](VEBLEN.md),
[THETA.md](THETA.md), [SHIFT.md](SHIFT.md), [SHIFT2.md](SHIFT2.md), [SHIFT3.md](SHIFT3.md), [SHIFT4.md](SHIFT4.md), [SHIFT5.md](SHIFT5.md), [SHIFT6.md](SHIFT6.md) and [SHIFT7.md](SHIFT7.md). A summary of the rounds 1–12 is in [THETA.md](THETA.md) §8.1, and a summary of the rounds 13–30 is in [ROUND2.md](ROUND2.md) §1.
Open: both halves above $`L(\omega+1)`$ (above $`X_4`$ without FRAG) in
$`R_2^C`$ and above $`\upsilon_{\omega^3}`$ in $`R_2^S`$; $`R_2^S = R_2^C`$, whose first case $`\nu_C = \nu_S`$ needs the reaches of long restarts; the
lower bound below $`\theta_0`$; whether the first fan needs an inaccessible; any InaccPsi upper bound for $`C^*_3`$, which lies below $`\omega_1^{CK}`$
(Carlson 2009, Thm 15.2).

**Lean** (the five files of this directory, built with the whole library):

- **Lemma L** (`CSet_inter_Om1`). For every $`\alpha`$: $`\mathrm{Cl}(\alpha, 0) \cap \Omega_1 = \psi_{\Omega_1}(\alpha)`$ as sets.
  So the countable values of the terms bounded by $`X`$ are exactly the ordinals below
  $`\psi_{\Omega_1}(X)`$ (`bounded_inter_Om1`), and those of the whole system are the ordinals below
  $`\psi_{\Omega_1}(\Lambda)`$ (`vals_inter_Om1`, `CSet_sub_Lam`). Each set is an initial segment of $`\Omega_1`$.
- **The three bounds** (`three_bounds`). $`\rho_A \lt \rho_B \lt \rho_S`$.
- **Lemma IS** (`lt_psi_one_mem_Vals`, `exists_NF_of_lt_psi_one`, `mem_Vals_of_lt_of_countable`). Every ordinal
  below $`\psi_{\Omega_1}(a)`$ is the value of a normal form; the countable values are downward closed.
  Proof idea: the least non-value $`\rho`$ is closed under $`+`$ and $`\varphi`$, and satisfies the defining
  condition of every $`\psi_{\Omega_1}(a)`$.
- **Lemma CONT** (`psi_one_iSup`). For increasing $`a_n`$: $`\psi_{\Omega_1}(\sup_n a_n) = \sup_n \psi_{\Omega_1}(a_n)`$.
- **Seven terms** (`LowTerms.lean`). For $`\eta \in \{0, 1, 2, \omega, \omega+1, \omega\cdot 2, \omega^2\}`$ the term
  $`u(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ with $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$ is a normal form, has
  this value, and the seven values increase; also $`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$.
- **The InaccPsi side of Theorem T-UP** (`ConjT.lean`). With $`A_\eta = \Omega_\omega + \theta\cdot\eta`$: the hypothesis (HA) of
  Theorem STEP holds for $`A_\eta`$, $`\eta \lt \omega^2`$ (`HA_A`); for any function $`u`$ that satisfies the start
  $`u(1) \le \psi_{\Omega_1}(\Omega_\omega)`$, the step of Theorem STEP and continuity at limits, the bound
  $`u(1+\eta) \le \psi_{\Omega_1}(A_\eta)`$ holds for $`\eta \le \omega^2`$ (`upper_bound`, `upper_bound_ww`), and every ordinal
  below $`u(\omega^2)`$ is the value of a normal form (`conjU`); two facts of ordinal arithmetic used in Lemma M
  (`arith_absorb`, `arith_lex`). Wilken's $`\upsilon`$, his systems and the map $`B`$ are not in Lean: the step is a
  hypothesis there, and Lean states it also for $`\xi = 0`$, which is trivial on paper but is not checked in Lean.
- **The InaccPsi side of Theorem T-LOW** (`LowerT.lean`). For any monotone $`u`$ with
  $`\psi_{\Omega_1}(\Omega_\omega) \le u(1)`$ and the step of LOW-STEP, assumed only for $`A = A_\eta`$: the bound
  $`\psi_{\Omega_1}(A_\eta) \le u(1+\eta)`$ for $`\eta \le \omega^2`$ (`lower_bound`, `lower_bound_ww`); with the hypotheses of
  `upper_bound` too, $`u(1+\eta) = \psi_{\Omega_1}(A_\eta)`$ (`conjT`, `conjT_ww`). LOW-0 and LOW-STEP are hypotheses; the map
  $`E`$ is not in Lean.

**Proved on paper and refereed.** Each review was adversarial (it tried to refute the result). No review found a
fatal or blocking point against a result listed here as proved (one claim with a blocking point is listed and
marked "not proved"). The other blocking points that were found are about open goals,
listed under "Not proved".

**Below $`\upsilon_{\omega\cdot\omega}`$.**

- **Theorem CORE-C.** Every ordinal below $`\upsilon_{\omega\cdot\omega}`$ is in $`\mathrm{Core}(R_2^C)`$. Proof: by the cap of
  Theorem EQB, no $`\alpha \lt \upsilon_{\omega\cdot\omega}`$ is $`\le_1`$ to everything above it; by Carlson 2009,
  Thm 14.14, the core is the least such ordinal (or all of Ord).
- **Lemma RESTR.** Below $`\Omega_\omega`$, the hull of InaccPsi and the hull of Pohlers's system with one
  inaccessible (Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof
  Theory 1998, Def 3.4.4.1) agree, and so do their $`\psi_{\Omega_{n+1}}`$. With the cited ordinals of
  $`\mathrm{ID}_{\lt\omega}`$ (Wilken 2021, §1; Pohlers 1998, Fig. 1) this gives
  $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ (cited, indirect). Two weak links are in the literature: Pohlers
  takes regular cardinals for recursively regular ordinals without proof, and Wilken states the ordinal
  of $`\mathrm{ID}_{\lt\omega}`$ without proof. Theorems STEP-0 and LOW-0 below now give
  $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ directly, so this citation is no longer needed.
- $`\psi_{\Omega_1}(0) = \Gamma_0`$, and $`\vartheta_0(\varepsilon_{\Omega+1}) = \psi_{\Omega_1}(\varepsilon_{\Omega_1+1})`$ (cited + RESTR).
- **Theorem MAIN.** These are equivalent: (i) every ordinal of $`\mathrm{Core}(R_2^C)`$ below
  $`\upsilon_{\omega\cdot\omega}`$ is the value of a countable InaccPsi term; (ii) every ordinal below
  $`\upsilon_{\omega\cdot\omega}`$ is; (iii) **Conjecture U**: $`\upsilon_{\omega\cdot\omega} \le D`$, where
  $`D = \sup_a \psi_{\Omega_1}(a)`$. Proof: CORE-C and Lemma IS.
- **Theorem STEP** (2026-10, 2 reviews). Wilken's points: $`\upsilon_0 = 0`$, $`\upsilon_{\xi+1} = T^{\upsilon_\xi} \cap \Omega_1`$, and the
  supremum at limits (Wilken 2020, Def 21.4; $`\upsilon_1 = T^1 \cap \Omega_1`$, p. 420). Let $`\tau`$ be $`1`$ or an
  $`\varepsilon`$-number, and let $`\Omega_\omega \le A`$, $`\tau \le \psi_{\Omega_1}(A)`$ and
  (HA) $`A \in \mathrm{Cl}(A+1, \psi_{\Omega_1}(A))`$. Then
  $`T^\tau \cap \Omega_1 \le \psi_{\Omega_1}(A + \theta)`$, with $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$.
  **STEP-0**: $`\upsilon_1 \le \psi_{\Omega_1}(\Omega_\omega)`$, without the proof-theoretic citation.
  Proof outline. Weiermann–Wilken 2011, Def 3.9 with Cor 3.7(f), shows that Wilken's stepwise system $`T^\tau`$
  and the simultaneous system $`\bar T^\tau`$ are the same set (Lemma SAME-SET). $`\bar T^\tau`$ has a domain rule
  (Lemma 4.3 there) and a comparison rule (Lemma 4.4 there). A map $`B`$ from $`\bar T^\tau`$ into InaccPsi sends
  $`\bar\vartheta_i(\alpha)`$ to $`\psi_{\Omega_{i+1}}(X_i + c_i(\alpha) + \mathrm{code}_i(\alpha))`$, where $`X_0 = A`$,
  $`X_i = 0`$ for $`i \ge 1`$, $`\mathrm{code}_i(\alpha) = \omega^{B(\alpha)}`$ for $`i \ge 1`$,
  $`\mathrm{code}_0(\alpha) = \psi_{\Omega_2}(\omega^{B(\alpha)}) \lt \theta`$, and $`c_i(\alpha)`$ lifts the argument above the image of
  the largest level-$`i`$ parameter of $`\alpha`$. Lemma N: each image argument lies in its own hull. Lemma M: $`B`$
  is strictly increasing. So $`T^\tau \cap \Omega_1 \le \sup B \le \psi_{\Omega_1}(A+\theta)`$. The new lemmas that carry
  the proof are SAME-SET, N, N2 and M. The second review also checked the map $`B`$ with its own code (no error).
- **Theorem T-UP** (2026-10, 2 reviews). $`\upsilon_{1+\eta} \le \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ for every $`\eta \lt \Gamma_0`$.
  Proof: induction with STEP; limits by Lemma CONT. The induction up to $`\eta = \omega^2`$ is in Lean
  (`ConjT.lean`).
- **Conjecture U is proved** (2026-10, 2 reviews): $`\upsilon_{\omega\cdot\omega} \le \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+2}) \lt D`$. By MAIN,
  every ordinal below $`\upsilon_{\omega\cdot\omega}`$ is the value of a countable InaccPsi normal form, with collapse
  arguments below $`\Omega_\omega + \omega^{\theta+2} \lt I_\omega`$ (Lemma L).
- **Theorem LOW-0** (2026-10, 1 review). $`\psi_{\Omega_1}(\Omega_\omega) \le \upsilon_1`$. With STEP-0:
  $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$, by comparing the two hulls directly.
- **Theorem LOW-STEP** (2026-10, 1 review). Let $`\sigma`$ be an $`\varepsilon`$-number, $`A = A_\eta`$ and
  $`\psi_{\Omega_1}(A) \le \sigma`$. Then $`\psi_{\Omega_1}(A + \theta) \le \bar T^\sigma \cap \Omega_1`$. It holds for every
  $`A \ge \Omega_\omega`$ whose last Cantor normal form summand is $`\ge \theta`$; without this condition it is not proved
  (e.g. $`A = \Omega_\omega + 1`$). Proof outline: a map $`E`$ from the InaccPsi normal forms below
  $`\psi_{\Omega_1}(A+\theta)`$ into $`\bar T^\sigma \cap \Omega_1`$ (the other direction from $`B`$):
  $`\varphi(x, y)`$ at level $`k`$ goes to $`\bar\vartheta_k(\Omega_{k+1}\cdot\omega^{E x} + E y)`$;
  $`\psi_{\Omega_{k+1}}(a)`$ goes to $`\bar\vartheta_k(\Omega_{k+1}^2 + F(E a))`$ with $`F(x) = \Omega_{m+1}^3\cdot\omega^x`$, $`m`$ the
  level of $`x`$ ($`F`$ lifts the code above every inner code, as the domain rule needs);
  $`\psi_{\Omega_1}(A + \zeta)`$ goes to $`\bar\vartheta_0(G(\mathrm{pmax}\,\zeta) + E\zeta)`$, where $`\mathrm{pmax}\,\zeta`$ is the
  largest $`\psi_{\Omega_2}`$-term at the top of $`\zeta`$ and $`G`$ lifts it the same way; parameters below $`\sigma`$
  stay. Lemma D: every image is in the domain (Weiermann–Wilken 2011, Lemma 4.3). Lemma M: $`E`$ is strictly
  increasing (Lemma 4.4 there). New lemmas that carry the proof: PARTS, PMAX, Q, Q1, D, M, ARG0, ARG1.
- **Theorem T-LOW** (2026-10, 1 review). $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) \le \upsilon_{1+\eta}`$ for every
  countable $`\eta`$. Proof: induction with LOW-0 and LOW-STEP; limits by Lemma CONT. With T-UP this gives
  **Theorem T** (§4). The induction up to $`\eta = \omega^2`$ is in Lean (`LowerT.lean`).
- **Theorem CORE-S** (2026-10). Every ordinal below $`\upsilon_{\omega^3}`$ is in $`\mathrm{Core}(R_2^S)`$ (from
  $`\upsilon_{\omega\cdot\omega}`$ on it uses Lemma FRAG, now proved, [RESTARTS.md](RESTARTS.md) §1). Below $`\upsilon_{\omega\cdot\omega}`$ the least closed sets of $`R_2^S`$
  are exactly the isominimal sets of $`R_2^C`$. Key step, Lemma FOLD: if $`f`$ is a covering, then the pointwise
  minimum of $`f`$ and the identity is again a covering, provided no two $`\lt_2`$-pairs are nested. Lemma NEST:
  this proviso fails above every chain of length 3. Here "least" in $`R_2^S`$ is Wilken's definition (2021,
  p. 6, for pure $`R_2`$), read for $`R_2^+`$.
- **Theorem LOW** (the summary above) follows from CORE-C, CORE-S, Conjecture U and Lemma L.

**Up to $`\upsilon_{\omega^3}`$, without FRAG** (2026-10, $`R_2^C`$). Extended to $`[0, \Xi_\omega]`$ by Theorem CORE-C$`^\Xi`$
([RESTARTS.md](RESTARTS.md) §3), to $`[0, \Lambda_\varepsilon)`$ and $`[0, \rho_{\Theta_P})`$ ([REACHES.md](REACHES.md) §2), and to
$`[0, \rho_{\Theta_A+\omega^2})`$ ([PINS.md](PINS.md) §2), and to $`[0, \rho_{\Theta_{d\omega}})`$, and to $`[0, \nu_C]`$ with $`\nu_C \gt \nu_P`$ ([BREAK.md](BREAK.md) §2, §4), now with $`\nu_C \ge X_4`$ ([SHIFT.md](SHIFT.md) §1), and, given FRAG, with $`\nu_C \ge X_n`$ for each point $`X_5, \dots, X_{23}`$ of §2 ([SHIFT6.md](SHIFT6.md) §2.1, §3.1), and $`\nu_C \ge L(\omega+1)`$ ([SHIFT7.md](SHIFT7.md) §1.1).

- Lemma PT, Theorem CORE-C3 (every ordinal $`\le \upsilon_{\omega^3}`$ is in $`\mathrm{Core}(R_2^C)`$, without FRAG) and its corollary $`m_3 \ge \upsilon_{\omega^3}`$ (1 review each) are in
  [ROUND2.md](ROUND2.md) §2.

**$`R_2^S`$ against $`R_2^C`$** (2026-10). These results are now in [THETA.md](THETA.md) §8.2: $`\beta_0`$, the least stage at which the two
structures differ, and $`\kappa_X`$, the least $`\kappa`$ that is $`\le_1^X`$ to everything above it; Lemma STAGE and Corollary FIRST (every $`R_2^S`$ relation with right end
at most $`\beta_0`$ holds in $`R_2^C`$, and now $`\beta_0 \ge \nu_C \gt \nu_P`$); Theorem LOC and the reductions of $`\nu_C = \nu_S`$ (now to a twisted upward rule,
[THETA.md](THETA.md) §4); Lemma UPG; KAPPA and CORE-EQ (if $`\max(\kappa_S, \kappa_C) \le \beta_0`$, AGR, the two cores are equal); the converse $`C \Rightarrow S`$ at stages of
agreement (CORE-1, LIM1, ONE-POINT, SUCC2, LIM2); DICH; R-INC; and the stages of type (ii) (MAX2, RED-d, FIRST2, UPCOPY, EQ-E with Conjecture CORE-2,
R-OM, and the open steps PIN and LOW).

**Moved to [ROUND1.md](ROUND1.md)** (first round, 2026-10): the finite-set tests T1, PR, T2 and CMP in $`R_2^S`$ (§1 there); the results toward an explicit
chain of length 3, among them ELEM, CLUB-1, CHAINS-S, HIGH, LOCAL-2, CHANG-2, SC2, I0-NOT-SIGMA2, REFORM, NO-PROMOTE, Lemma K and COLLAPSE-FAIL (with its blocking point) (§2 there);
and the reductions toward the lower bound, I-FREE, OE, EPS-RED, FS-OE, RED-BMS, S-RED, MU-A, UNIF-V, MU-B (with its blocking point, against its use for the core), MU-0 and MU-B0
(§3 there; $`G_B`$ below is the fragment of MU-B). Write $`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$; by Lemma I-FREE the countable normal forms without an inaccessible symbol are exactly those below $`\theta_0`$.

**Chains.** A chain of length $`n`$ is $`n`$ additive principal numbers that are pairwise $`\le_2`$. $`C^*_n`$ is the
pointwise least one.

- **Theorem CC** (in $`R_2^C`$). $`\mathrm{Core}(R_2^C) = \sup_n \max C^*_n`$, and a pattern with $`n`$ additive principal
  numbers has its least realization below $`\max C^*_{n+1}`$. (For $`R_2^S`$ this is open; AGR gives the same core.)
- **Theorem DOM₂** (2026-10, $`R_2^C`$). Let $`C^*_3 = \{c_0 \lt c_1 \lt c_2\}`$ and $`m_3 = \min\{m : m \le_1 c_0\}`$. A pattern
  with no chain of length 3 has its least realization below $`m_3`$, and $`m_3 \lt c_0`$. **Theorem SHARP**: the union of
  the isominimal sets with no chain of length 3 is exactly $`[0, m_3)`$. **DOM₁′**, the same for patterns without
  $`\lt_2`$-pairs: their union is $`[0, m_2)`$, with $`m_2`$ the least $`\le_1`$-predecessor of $`\min C^*_2 = \upsilon_\omega`$,
  and $`m_2 = \upsilon_1`$ given the cited core of $`R_1^+`$ and Theorems A, EQ.
- Facts on $`C^*_3`$, the fans and the chains of pairs $`\mathrm{CH}_k`$ (2026-10): lower bounds for $`m_3`$, $`c_0`$, the fans and $`m_F`$, and the native bounds for $`\iota(\mathrm{CH}_k)`$, are in
  [ROUND2.md](ROUND2.md) §3. The latest native bound is $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$, with the stage labels as points inside the pair of the code
  ([SHIFT6.md](SHIFT6.md) §3.3; before, $`\psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1)`$, and $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ with a growing chain number, §1.3 there; stage labels of every finite level would give $`\psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega)`$, but they rest on a referee's repair of one blocking point that has had no second check, [SHIFT7.md](SHIFT7.md) §1.3). Also $`C^*_2 = \{\upsilon_\omega, \upsilon_{\omega+1}\}`$.
- Lemma TOP2 ($`m_3`$ is a limit of chains of length 2), Lemma REL (a restart above $`\psi_{\Omega_1}(A)`$ costs $`+\theta`$ per step), the small lemmas PRINC, ISO-UNION, HULL and
  DOM₁, and the chains made by $`\Phi_3`$ (Theorem A: the output relation has no chain of length 3; Theorem B, Corollary C, Lemma LAM, BAR_R, CONE) are in [ROUND2.md](ROUND2.md) §4.

**Not proved:**

- **The claim above $`L(\omega+1)`$ given FRAG, and above $`X_4`$ without FRAG,** in $`R_2^C`$, and above $`\upsilon_{\omega^3}`$ in $`R_2^S`$, both halves (an InaccPsi
  upper bound for $`\nu_C`$ would give it up to $`\nu_C`$; it needs only two $`\le_1`$-statements (P) and (Q) at one named pair, both about reaches of long
  restarts, [SHIFT.md](SHIFT.md) §1; (Q) cannot come from the known upper bounds on the reaches below the left end, §8.1; (P) needs reaches across an uncountable offset, §9.1, that is past the first index fixed point, [SHIFT2.md](SHIFT2.md) §1.1; the tools now reach the η-offsets below $`\theta`$, with exact caps by order type, [SHIFT3.md](SHIFT3.md) §1.1, §2.1, then the η-offsets below $`\psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ and the codes below $`G(\Omega_3+1)`$, [SHIFT4.md](SHIFT4.md) §1.1, §1.4, then the codes below $`G(\hat\zeta_2)`$, §2.1, §2.2 there, then the codes below $`G(\hat\zeta_\varepsilon)`$ with the landing cap, [SHIFT5.md](SHIFT5.md) §1.1, then the codes below $`G(\hat\zeta_H)`$ with a hull cap (the landing cap is false further up), §2.1 there, then the codes below $`G(\theta_4\cdot\omega^2)`$ with a cap that needs no hull and the codes below $`G(\hat\zeta_{23})`$, [SHIFT6.md](SHIFT6.md) §1.1, §2.1, with the repair of §3.1 there, then every code below $`P'`$ with the relative far pin at every depth, which gives $`\nu_C \ge L(\omega+1)`$, [SHIFT7.md](SHIFT7.md) §1.1; (P) still needs the reaches at the code $`P'`$ at level 2). The reaches of the restarts
  above $`\Theta_A`$ (the reach at $`\Theta_A`$ itself is now known), and the rest of [SHIFT7.md](SHIFT7.md) §1.6, [COVER.md](COVER.md) §9, [BREAK.md](BREAK.md) §10, [PINS.md](PINS.md) §6, [REACHES.md](REACHES.md) §7 and [RESTARTS.md](RESTARTS.md) §6.
- **$`R_2^S = R_2^C`$**: the converse $`C \Rightarrow S`$ for $`\le_1`$ at a successor stage $`\beta \gt \kappa_C`$ with
  $`\alpha \notin G_C`$, and for $`\le_2`$ at stages of type (ii) (this needs an upward transfer of $`\Pi_2`$ sentences, which
  neither upward 2-reflection nor liftings give; it is now one pair $`(a^*, \beta)`$ per stage, and below $`\kappa_C`$ it is
  Conjecture CORE-2; left: PIN and LOW); Σ2-GAP, INC, W(C), (R), AGR, and $`\beta_0 = \infty`$ (these words are defined in [THETA.md](THETA.md) §8.2).
  Theorem CC and all certificates are about $`R_2^C`$.
- **The lower bound below $`\theta_0`$** (referee: blocking gap toward this goal, not an error; the 26 undecided limit jumps of
  the sample above $`V_3`$ are now proved, [FANFREE.md](FANFREE.md) §1; the step below SRO is now proved for every $`n`$ on all 3,166 sample
  matrices, [FANFREE.md](FANFREE.md) §7.1, §10.1, [VEBLEN.md](VEBLEN.md) §3, §10, [THETA.md](THETA.md) §3, §9.3, [SHIFT.md](SHIFT.md) §3, §8.3, §9.3, [SHIFT2.md](SHIFT2.md) §1.3, §2.3, §3.3, [SHIFT3.md](SHIFT3.md) §1.3, §2.3, [SHIFT4.md](SHIFT4.md) §1.3, §2.3): an order embedding
  $`\mu`$ of all $`\varepsilon`$-number terms below $`\theta_0`$ into standard trio matrices below SRO, and the local step
  of S-RED for all matrices below SRO. Outside $`G_B`$ are four families: (M1) uncountable $`\kappa`$, $`c`$ or $`g`$ in a
  summand; (M2) successor indices such as $`\Omega_{\xi+1}`$; (M3) uncountable indices such as $`\Omega_{\Omega_\omega}`$; (M4)
  the whole base below $`\psi_{\Omega_1}(\Omega_\omega)`$ ($`\varepsilon_1`$, $`\Gamma_0`$, $`\varphi(a, b)`$ with $`a \ge 1`$, …). (M4) at
  level 0 is done (MU-0, MU-B0) but adds nothing to the core; left: (M4) at level $`\ge 1`$ (Lemma TR1), (M1)–(M3), and the
  local step above $`V_3`$. Inside the range of Wilken's $`\upsilon`$ the bound comes from the caps instead; they now give
  $`[0, \rho_{\Theta_P})`$ (CORE-C$`^+`$, [REACHES.md](REACHES.md) §2). Then the gap $`[\theta_0, \psi_{\Omega_1}(I_0))`$, which
  needs $`\psi_{I_0}`$-collapses.
- **$`C^*_3`$ explicitly.** Conjecture C3′ (from Wilken's least 3-chain of pure $`R_2`$, 2021, pp. 19–21, CH and
  Lemma REL), with $`P = \theta = \psi_{\Omega_2}(\Omega_\omega)`$ and $`E = \varepsilon_{I_0+1}`$: $`m_3 = \psi_{\Omega_1}(E)`$ and
  $`C^*_3 = \{\psi_{\Omega_1}(E + P),\ \psi_{\Omega_1}(E + \omega^{P+1}),\ \psi_{\Omega_1}(E + \omega^{P+1} + P)\}`$. All are normal forms
  between $`\psi_{\Omega_1}(I_0)`$ and $`\psi_{\Omega_1}(I_1)`$ (checked, Python and Lean). The earlier guess had
  $`E + \Omega_\omega`$ in place of $`E`$ in the three chain terms; by REL it does not fit the reading it came from (the
  $`\upsilon`$-hierarchy restarted above $`m_3`$), because a restart costs $`+P`$, not $`+\Omega_\omega`$ (proved as a
  dichotomy, 1 review). The reading itself is now refuted: the restarted triple above a point is never a chain
  (C3′-FALSE, 1 review, [REACHES.md](REACHES.md) §5; it uses Lemma LEFT, which is now proved,
  [BREAK.md](BREAK.md) §1), so the numeric C3′ has no derivation left. The corrected shape C3′′ is false too: $`c_0, c_1, c_2`$
  are all limit points of the class $`C_{\omega^\omega}`$ (Theorem C3′′-FALSE, [BREAK.md](BREAK.md) §3). A chain of length 3 is exactly a fan with
  infinitely many successors whose limit is a left end (Theorem CF, unconditional); in $`R_2^C`$ this is now a $`\le_1`$-condition on the right ends of one point (Theorem CP3,
  [COVER.md](COVER.md) §1), which characterizes the chain but does not locate it. Upper half open: the
  known $`\le_2`$ relations of $`R_2^C`$ (up to $`\Lambda_\varepsilon`$) form no chain of length 3 (Theorem BLK$`^O`$); a chain must be in the
  seed of Carlson's generation (NO-GEN); set-theoretic
  reflection gives chains only above $`\omega_1^{CK}`$ (HIGH), and the $`\le_1`$-reach alone does not give a chain
  (NO-PROMOTE). Carlson 2009, Thm 15.2 gives $`c_2 \lt \omega_1^{CK}`$, but no bound by an InaccPsi term is proved ([COVER.md](COVER.md) §5.2). Such a bound needs only one
  pair $`a \lt_2 c`$ below it and a second left end $`b \lt_2 c`$ between (Lemma CRIT, [COVER.md](COVER.md) §6.2, 1 review); splitting it into a start
  and a cost per step is equivalent to the bound itself. Lower half open: it needs the lower bound program below $`\theta_0`$ with patterns without a chain of
  length 3.
- That $`\Phi_3(M)`$ is a pattern. Then it has no chain of length 3 (Corollary C, [ROUND2.md](ROUND2.md) §4), and DOM₂ bounds its point by $`m_3`$.
  The output relation itself has no such chain (Theorem A, proved); for its closure this is BAR_R (checked only).

## 4. Names of Wilken's points (Theorem T)

**Theorem T** (proved; upper half T-UP 2 reviews, lower half T-LOW 1 review). With
$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$, for every $`\eta \lt \Gamma_0`$, in particular for $`\eta \le \omega^2`$, and by Theorem T+
(2 reviews, [RESTARTS.md](RESTARTS.md) §4) for every $`\eta`$ below the first fixed point $`\Xi_1`$ of $`\iota \mapsto \upsilon_\iota`$
(beyond, Theorem T++ of [REACHES.md](REACHES.md) §2 names every $`\Xi_\alpha`$ and the points between them up to $`\Phi_1`$, and
Theorem GEN of [PINS.md](PINS.md) §3 names the $`\upsilon`$-points below $`\upsilon^*`$, now known to be $`\psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ ([THETA.md](THETA.md) §1):
$`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) = \upsilon_{1+\iota(\eta)}`$ for every $`\eta`$ in the set $`D`$ of the $`\eta \lt \Omega_2`$ that give a normal form, with
$`\iota(\eta)`$ the order type of $`D \cap \eta`$; GEN-EXT extends this to $`\eta \lt \Omega_\omega\cdot\omega`$, [BREAK.md](BREAK.md) §2, and GEN⁺, a case of GEN-EXT, states it on the set of all $`\eta \lt \Omega_\omega`$ that give a normal form, [THETA.md](THETA.md) §1, where it was labelled a transfer; it is proved by citing GEN-EXT, [SHIFT4.md](SHIFT4.md) §2.4; GEN-ALL extends it to every $`\eta`$ with $`\eta \in \mathrm{Cl}(\Omega_\omega + \theta\cdot\eta, \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta))`$, so $`\psi_{\Omega_1}(I_\omega)`$ is itself a $`\upsilon`$-point, [SHIFT5.md](SHIFT5.md) §1.3):

```math
\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta).
```

The upper half "$`\le`$" is Theorem T-UP, the lower half "$`\ge`$" is Theorem T-LOW (§3). Lean has the induction
up to $`\eta = \omega^2`$, with the steps as hypotheses (`ConjT.lean`, `LowerT.lean`).

| $`\eta`$ | point | term |
|---|---|---|
| $`0`$ | $`\upsilon_1`$ | $`\psi_{\Omega_1}(\Omega_\omega)`$ |
| $`1`$ | $`\upsilon_2`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta)`$ |
| $`2`$ | $`\upsilon_3`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot 2)`$ |
| $`\omega`$ | $`\upsilon_\omega`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1})`$ |
| $`\omega+1`$ | $`\upsilon_{\omega+1}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1} + \theta)`$ |
| $`\omega\cdot 2`$ | $`\upsilon_{\omega\cdot 2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1}\cdot 2)`$ |
| $`\omega^2`$ | $`\upsilon_{\omega^2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+2})`$ |

Only $`\psi_{\Omega_1}`$, $`\psi_{\Omega_2}`$ and $`\Omega_\omega`$ occur: no inaccessible is needed below
$`\upsilon_{\omega\cdot\omega}`$. The naive guess $`\upsilon_\iota = \psi_{\Omega_1}(\Omega_\omega\cdot\iota)`$ is too large from
$`\iota = 2`$ on (Lean: $`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$). Reason for
$`+\theta`$: in the proof of STEP, the level-0 code $`\mathrm{code}_0`$ stays below $`\theta`$. The translation `por/tr3.py` of
[R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md) gives the same points for the matrices of Theorem S (checked).

## 5. The route: a tree of lemmas

Three routes: B gives the upper bound, A is a full analysis, L gives the lower bound.

- **W** Wilken's claim, $`\mathrm{Core}(R_2^+) = \psi_{\Omega_1}(I_\omega)`$ — open
  - **Low** below $`\upsilon_{\omega\cdot\omega}`$, in $`R_2^C`$ and $`R_2^S`$ — proved (Theorem LOW)
    - Conjecture U — proved (STEP, T-UP)
    - Theorem T, the exact names for $`\eta \lt \Gamma_0`$ — proved (T-UP, T-LOW); the names of every $`\upsilon`$-point below $`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ — proved (GEN-ALL; [SHIFT5.md](SHIFT5.md) §1.3)
    - $`\mathrm{Core}(R_2^S)`$ contains all of $`\upsilon_{\omega\cdot\omega}`$ — proved (CORE-S)
    - in $`R_2^C`$ up to $`\upsilon_{\omega^3}`$, without FRAG — proved (CORE-C3, PT)
    - in $`R_2^C`$ up to $`\Phi_1`$, and the core of $`R_2^C`$ up to $`\rho_{\Theta_P}`$ — proved (T++, PHI, CORE-C$`^O`$, CORE-C$`^+`$;
      [REACHES.md](REACHES.md))
    - in $`R_2^C`$ up to $`\Lambda_\varepsilon`$, and the core of $`R_2^C`$ up to $`\rho_{\Theta_A+\omega^2}`$ — proved (GEN, NAME-V,
      NAME-OFFSET, CORE-C$`^A`$; [PINS.md](PINS.md))
    - in $`R_2^C`$ up to $`\rho_{\Lambda'+\omega^2}`$, with the reaches there in closed form and the name of $`\Theta_P`$ — proved (NAME-OFFSET-Z, STRUCT′,
      THETA-P; [FANFREE.md](FANFREE.md) §10.4)
    - in $`R_2^C`$ up to $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$, with the reaches there in closed form — proved (VEB-THETA, GAM-THETA′, EXACT-G⁺, PSI2⁺,
      NAME-OFFSET-G⁺, STRUCT″; [VEBLEN.md](VEBLEN.md) §1, §8); up to $`H(\varepsilon_{\theta+\omega} + \omega^2)`$, with $`\Theta_1 = H(\theta)`$ and $`\Theta_A = H(\varepsilon_{\theta+\omega})`$ — proved
      (PAR-SAME with L3, B-PAR, PAR-ψ, H3; THETA1 and THETA-A 2 reviews; [THETA.md](THETA.md) §1)
    - in $`R_2^C`$ up to $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ and up to $`\nu_P = X_2`$ — proved, 2 reviews (UPS\*, U\*, F1, GEN⁺, SLOW$`_\zeta`$, Lemma S, R-CAP, F2;
      [THETA.md](THETA.md) §1, §9.1); the names of $`\Theta_\delta`$, $`\Theta_{d\omega}`$, $`\Lambda^*`$, $`\nu_P`$ — proved (SSTEP$`_\zeta`$, HULL-SEG, REAL, BRACKET, NAMES-EQ, with the
      amended formal reach, 2 reviews; [THETA.md](THETA.md) §9.1, [SHIFT.md](SHIFT.md) §1); up to $`X_3`$, with $`\nu_C \ge X_3`$ — proved, no FRAG (Theorem X3); up to $`X_4`$,
      with $`\nu_C \ge X_4`$ — proved, no FRAG (TOP-REG⁺, R-CAP\*, Theorem X4; [SHIFT.md](SHIFT.md) §1); up to $`X_5`$, with $`\nu_C \ge X_5`$ — proved given FRAG
      (XA, EXACT-C, PIN-IDX, R-CAP-ξ, FAR, Theorem X5; [SHIFT.md](SHIFT.md) §8.1); up to $`X_8`$, with $`\nu_C \ge X_8`$ — proved given FRAG, with no outline input
      (OFF, FAR-PIN, TOP-REG-FAR, MULTI-RC, R-CAP-FAR, Theorem X8; 2 reviews; [SHIFT.md](SHIFT.md) §9.1); up to $`X_9`$, with $`\nu_C \ge X_9`$ — proved given FRAG
      (OFF-INF, MULTI-RC\*, PHI\*, R-CAP-FAR\*, Theorem X9; 2 reviews; [SHIFT2.md](SHIFT2.md) §1.1, §2.1); up to $`X_{11}`$, with $`\nu_C \ge X_{11}`$ — proved given FRAG
      (D′-UNC, DICT, EXACT-V, MULTI-RC$`^U`$, PHI$`^U`$, R-CAP$`^U`$, CEIL$`^U`$, Theorem X11; [SHIFT2.md](SHIFT2.md) §2.1); up to $`X_{12}`$, with $`\nu_C \ge X_{12}`$ — proved given FRAG
      (NO-PHI, PSI2-χ, EXACT-O, EXACT-LONG, R-CAP$`^\chi`$, CEIL$`^\chi`$, Theorem X12; [SHIFT2.md](SHIFT2.md) §3.1); up to $`X_{13}`$, with $`\nu_C \ge X_{13}`$ — proved given FRAG
      (TOP-REG-FAR′, VEB-THETA$`^\vartheta`$, PSI2-θ, EXACT-O$`^\vartheta`$, R-CAP$`^\vartheta`$, CEIL$`^\vartheta`$, Theorem X13; [SHIFT3.md](SHIFT3.md) §1.1); up to $`X_{14}`$, with $`\nu_C \ge X_{14}`$ — proved given FRAG
      (PSI-n, CNST$`^n`$, EXACT-O$`^n`$, R-CAP$`^\theta`$, CEIL$`^\theta`$, Theorem X14; [SHIFT3.md](SHIFT3.md) §2.1); up to $`X_{15}`$, with $`\nu_C \ge X_{15}`$ — proved given FRAG
      (CLOSED-REACH, TOP-REG$`^\omega`$, EXACT-CL, the tier below $`\zeta^*`$, Theorem X15; [SHIFT4.md](SHIFT4.md) §1.1); up to $`X_{16}`$, with $`\nu_C \ge X_{16}`$ — proved given FRAG
      (PLATEAU, D-UNC$`^Z`$, the θ⁺ tier, R-U, Theorem X16; [SHIFT4.md](SHIFT4.md) §1.4; both 2 reviews, §2.1); up to $`X_{17}`$, with $`\nu_C \ge X_{17}`$ — proved given FRAG
      (ROOT-LOC, ENUM, EXACT-CL\*, the tier up to $`\Omega_3\cdot\omega`$, Theorem X17; [SHIFT4.md](SHIFT4.md) §2.1); up to $`X_{18}`$, with $`\nu_C \ge X_{18}`$ — proved given FRAG
      (PHI-COMM, READ on the ordinal side, the caps below $`G(\hat\zeta_2)`$, Theorem X18; [SHIFT4.md](SHIFT4.md) §2.2; 2 reviews with the repairs of [SHIFT5.md](SHIFT5.md) §1.1); up to $`X_{19}`$, with $`\nu_C \ge X_{19}`$ — proved given FRAG
      (SEP$`^{\mathrm{near}}`$, NO-LIT, EXACT-LONG⁺, FAR-PIN$`^L`$, TOP-REG-LAND, LAND-CAP, Theorem X19; [SHIFT5.md](SHIFT5.md) §1.1); up to $`X_{21}`$, with $`\nu_C \ge X_{21}`$ — proved given FRAG
      (THETA$`^G`$, EXACT-LONG$`^G`$, EXACT-F, NO-READL, CAP$`^\sharp`$, Theorem X21; [SHIFT5.md](SHIFT5.md) §2.1; 2 reviews with the repairs of [SHIFT6.md](SHIFT6.md) §1.1); up to $`X_{22}`$ and $`X_{23}`$, with $`\nu_C \ge X_{23}`$ — proved given FRAG
      (CUSHION, Theorem X22, CUSHION$`^\varepsilon`$, Theorem X23, with the exact long reaches repaired by the landing code: AGREE, EXACT-LONG$`^{(3)\sharp}`$; [SHIFT6.md](SHIFT6.md) §1.1, §2.1, §3.1; 1 review of the repair); up to $`L(\omega+1)`$, with $`\nu_C \ge L(\omega+1)`$ — proved given FRAG
      (FAR-PIN$`^{L,\mathrm{rel}}`$, LAND$`^\omega`$, EX$`^w`$ and CAP-0 below $`P'`$, CAP-1, NU-LOW″⁺; [SHIFT7.md](SHIFT7.md) §1.1; 1 review)
    - the core of $`R_2^C`$ up to $`\rho_{\Theta_{d\omega}}`$, and on $`[0, \nu_C]`$ with $`\nu_C \gt \nu_P`$ — proved (CORE-C$`^{d\omega}`$, CAP, NU-CT; [BREAK.md](BREAK.md))
  - **B** upper bound $`\mathrm{Core}(R_2^+) \subseteq \psi_{\Omega_1}(I_\omega)`$ — open
    - B0 reduction to least chains (Theorem CC) — proved for $`R_2^C`$
      - B0-S the same for $`R_2^S`$ — open; it follows from AGR
        - $`S \Rightarrow C`$ — proved up to $`\beta_0`$ (STAGE, FIRST); beyond $`\beta_0`$ open (not inductive by itself)
        - $`C \Rightarrow S`$ at stages of agreement — $`\le_1`$ proved below $`\kappa_C`$, at limits, at $`\alpha+1`$ and under UPG;
          $`\le_1`$ at successors above $`\kappa_C`$ open; $`\le_2`$ proved at successors and LIM2, open at $`\omega^\lambda`$ (DICH)
          - $`\le_2`$ at stages of type (ii): reduced to one pair and to $`\Pi_2`$-UP (MAX2, RED-d, UPCOPY), equivalent below
            $`\kappa_C`$ to Conjecture CORE-2 (EQ-E) — proved; PIN and LOW — open
        - (R) iff $`\kappa_C \le_1^S \Omega_1`$, and AGR iff (E) and (R) — proved (R-OM)
    - B1 explicit chains of every length $`n`$ below $`\psi_{\Omega_1}(I_\omega)`$ as InaccPsi values — open; a bound needs only one pair with one
      more point (CRIT, [COVER.md](COVER.md) §6.2), but no InaccPsi term is proved to bound $`x_F`$ or $`c_0`$
      (conjecture for $`n = 3`$ in §3); a bound for $`m_F`$ is a bound for one sequence of chains of pairs ([FANFREE.md](FANFREE.md) §4); a bound $`\iota(\mathrm{CH}_2) \lt t`$ is exactly three
      relations at one point below $`t`$ ([FANFREE.md](FANFREE.md) §7.4)
    - B-NU an InaccPsi upper bound for $`\nu_C`$ — open; reduced to two $`\le_1`$-statements (P) and (Q) at one named pair, both about reaches of
      long restarts (NU-MIN, CPB-S; the shift criterion SHIFT is proved, its named instance is open; [SHIFT.md](SHIFT.md) §1); a pair with both has its
      right end $`\ge L(\omega+1)`$ given FRAG, and (Q) cannot come from the known upper bounds on the reaches below the left end (CL, P-LOW, Q-OBST; [SHIFT.md](SHIFT.md) §8.1);
      (P) needs reaches across an uncountable offset, and (Q) can be weakened to a statement (Q′) on one isominimal set (P-UNC, CPB-LOC; [SHIFT.md](SHIFT.md) §9.1);
      (P) needs upper bounds for reaches and codes past the first index fixed point ([SHIFT2.md](SHIFT2.md) §1.1); now exact caps by order type, sharp crossing and η-offsets go up to
      $`\theta`$ ([SHIFT2.md](SHIFT2.md) §2.1, §3.1, [SHIFT3.md](SHIFT3.md) §1.1, §2.1; the conjecture EXACT-PHI is false), then, with closed reaches (the literal rule TOP-REG past $`\delta_1\cdot\omega`$ is false, its corrected form is proved), exact caps up to
      $`\varphi(\omega, G(\omega+1)+1)`$, long restarts with $`D \lt G_2`$, η-offsets below $`\psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ and codes below $`G(\Omega_3+1)`$ ([SHIFT4.md](SHIFT4.md) §1.1, §1.4), then exact reaches below $`G_2`$ (GAP$`_j`$, ROOT-CL) and codes below $`G(\hat\zeta_2)`$ ([SHIFT4.md](SHIFT4.md) §2.1, §2.2), then, with the landing cap (the cap whose target lies in the region of the last prefix restart is false at $`\theta_3\cdot\omega^2`$) and exact long reaches for $`D \lt \varepsilon_{G_2+1}`$, codes below $`G(\hat\zeta_\varepsilon)`$ ([SHIFT5.md](SHIFT5.md) §1.1), then, with exact long reaches up to the first index fixed point and a hull cap (the landing cap is false further up), codes below $`G(\hat\zeta_H)`$ ([SHIFT5.md](SHIFT5.md) §2.1), then codes below $`G(\theta_4\cdot\omega^2)`$ with a cap that needs no hull and codes below $`G(\hat\zeta_{23})`$ ([SHIFT6.md](SHIFT6.md) §1.1, §2.1, with the repair of §3.1 there), exact landing reaches on the family $`[G(\hat\zeta_3), G(\hat\zeta_3+\Omega_2))`$ and on the $`\varepsilon`$ tier from $`G(\hat\zeta_G)`$ ([SHIFT6.md](SHIFT6.md) §2.1, §2.2, §3.1), and lower bounds for the reaches of all codes below $`P'`$ ([SHIFT6.md](SHIFT6.md) §3.2); then exact reaches and caps for every code below $`P'`$ at levels 1 and 2 with the relative far pin at every depth ([SHIFT7.md](SHIFT7.md) §1.1); (P) still
      needs the reaches at the code $`P'`$ at level 2 (the restarts of code $`P'`$ across the offset $`\omega^{P'+1}`$)
    - B2 a finite-set test for $`\lt_2`$ in $`R_2^+`$ — proved (T1, T2); whether the uniform form (one copy for all
      $`k`$) is also necessary is open in $`R_2^+`$ (Wilken 2021, p. 6, says it is for pure $`R_2`$)
    - B3 base changes that keep $`0, +, \le, \le_1, \le_2`$ — proved where $`R_2^+`$ is skeletal (Theorem FRAG2; FRAG itself is
      proved; its map equals a substitution map, FRAG-SUBST, [BREAK.md](BREAK.md) §4); beyond the skeleton, proved with their
      hypotheses (FRAG2-W, FRAG2-C, FRAG2-1E); several non-$`\upsilon`$ bases at once (FRAG-E) — open, very hard
    - B4 the $`\le_2`$-pairs among the points that B3 moves — proved below $`\nu_P`$ in $`R_2^S`$ and below $`\rho_{\Theta_A+\omega^2}`$ in both
      structures (SKEL, BLK$`^O`$, EQB-A), and up to the first non-skeletal point $`\nu`$ in $`R_2^S`$ (SKEL⁺, FIRST-PAIR); every
      $`\lt_2`$-left end is a $`\upsilon_\lambda`$ with $`\lambda`$ a limit (LEFT, now with no hypothesis: INC1
      and NOBAD, [BREAK.md](BREAK.md) §1); in $`R_2^S`$, at every countable ordinal, every pair is a standard pair or joins two restarts, so
      RIGHT (every right end is a $`\upsilon`$-point) holds in $`R_2^S`$ (SKEL$`^\infty`$, [COVER.md](COVER.md) §5.1);
      the pairs between restarts above $`\nu`$ in full, and RIGHT in $`R_2^C`$ above $`\beta_0`$ — open
    - B5 assembly B2 + B3 + B4 — proof form only
    - B-PT proof-theoretic variant: theories with $`n`$ inaccessibles prove "a chain of length $`n`$ exists" —
      open; needs a set-theoretic condition for $`\lt_2`$ that is not known
  - **A** full analysis — open
    - A1 hull systems over every base, with simultaneous collapsing functions for all $`\Omega_\xi`$ and $`I_n`$,
      compared with InaccPsi — open, high (the map $`B`$ of STEP does this below $`\Omega_\omega`$, one way; at the level of $`\Omega_1`$, Wilken's
      levels below $`\Omega_1^2 + \Omega_1`$ are the Veblen functions and $`\Gamma`$, VEB-THETA and GAM-THETA, [VEBLEN.md](VEBLEN.md) §1; Wilken's system and the simultaneous system of Weiermann–Wilken have the same parameters, PAR-SAME, and the maps $`E`$ of LOW-STEP and $`B`$ of STEP work at the bases $`\psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$, [THETA.md](THETA.md) §1, §9.1)
    - A2 a structure theorem for $`\le_1`$, $`\le_2`$ of $`R_2^+`$ up to the bound (the analogue of Wilken 2021,
      Thm 4.2); the results of [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md) are this theorem below
      $`\upsilon_{\omega^3}`$, Theorem BLK$`^O`$ extends it with exact reaches to $`\Lambda_\varepsilon`$, Theorem EXACT-A to $`\Theta_A`$
      ([PINS.md](PINS.md)), STRUCT′ writes it with names up to $`\rho_{\Lambda'+\omega^2}`$ ([FANFREE.md](FANFREE.md) §10.4) and STRUCT″ up to $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ ([VEBLEN.md](VEBLEN.md) §8), KV-NAMES reads the
      Klammer reaches below $`\nu_C`$ off the names (same place), the value at $`\Theta_A`$ and the landmarks $`\Theta_\delta`$, $`\Theta_{d\omega}`$ ([BREAK.md](BREAK.md) §4) with their names and those of $`\Lambda^*`$, $`\nu_P`$ ([THETA.md](THETA.md) §9.1), the exact reaches of the restarts with countable exponent and of $`\Lambda^*`$ (EXACT-C, LONG-G2), the first exact reach with an uncountable exponent and lower bounds for all long restarts (EXACT-W, LONG-ALL, RL-UP; [SHIFT.md](SHIFT.md) §9.1), lower bounds for reaches across regions (CROSS, RL-UNC, RL-2; [SHIFT2.md](SHIFT2.md) §1.1), the exact reaches of the short restarts with exponent below $`\psi_{\Omega_2}(\Omega_2)`$ and the sharp crossing at index fixed points (EXACT-V, CROSS-SHARP; [SHIFT2.md](SHIFT2.md) §2.1), and the exact tails $`\delta\cdot 2 + t`$ of long restarts (TAIL-MIN, BASE0-TAIL; [SHIFT.md](SHIFT.md) §8.1, §8.4), Theorem SKEL gives it in
      $`R_2^S`$ on $`[0, \nu_P)`$ ([REACHES.md](REACHES.md)), SKEL⁺ up to $`\nu`$ ([BREAK.md](BREAK.md) §2), and the level-0 description of $`R_2^S`$ at every
      countable ordinal (SKEL$`^\infty`$, [COVER.md](COVER.md) §5.1); the first block of every level of nested pairs (LIFT-0,
      [BREAK.md](BREAK.md) §5), and every block of every level below $`T_\omega`$ (SH, [BREAK.md](BREAK.md) §7.1) — proved; the order type of each level
      ($`o_k = \omega`$, equivalent to a finite base change between its gaps, GI) — proved in $`R_2^C`$ (Theorem O$`^C`$, [BREAK.md](BREAK.md) §8.1,
      1 review), open in $`R_2^S`$ (reduced to an $`R_2^S`$ form of Carlson's minimality and one pinning statement, [COVER.md](COVER.md) §4; that minimality
      holds up to $`\beta_0`$, §5.4); NOLIM inside the gaps of level 2 — proved in $`R_2^C`$ (NOLIM$`^C`$, [COVER.md](COVER.md) §3 and §5.1), in $`R_2^S`$ proved
      when there is no ghost, open above $`\beta_0`$ when there is one; its reaches
      and names — open, very hard
    - A3 least realizations as terms — open
    - A4 **Conjecture CH**: the least chain of length $`k+2`$ needs $`k`$ inaccessibles — conjecture
    - A5 every term below the bound is the value of a pattern — open
    - A6 $`R_2^S = R_2^C`$ everywhere — open (known below $`\beta_0 \gt \upsilon_{\omega\cdot\omega}`$); its first case $`\nu_C = \nu_S`$ is one $`\Sigma_2`$ statement
      (EQ), implied by a segment condition SC that is proved on the first block ([COVER.md](COVER.md) §6.3), and on the initial part of each
      segment at outline level ([FANFREE.md](FANFREE.md) §3), now proved below the first limit of critical indices ([FANFREE.md](FANFREE.md) §7.3) and on a larger part ([FANFREE.md](FANFREE.md) §10.3);
      left: SC at the long restarts, which the reduction always needs; directly in $`\Sigma_2`$ form, every extension above the copy is matched
      (TOP, [VEBLEN.md](VEBLEN.md) §4); left there: a local base change and translations with a fixed finite set below the copy; the local part
      holds on the zone of the base change given an open condition (HC), but there the translations fail ([VEBLEN.md](VEBLEN.md) §11); now (HC) is proved,
      the reduction is repaired, and everything except "twisted triples" is matched ([THETA.md](THETA.md) §4); twisted copies exist for small closed-form
      skeletons, several blocks at once included ([THETA.md](THETA.md) §9.4); (PROF) holds for every symbol, one more layer of closed reaches is known, and one explicit
      property is a ghost iff the tails of the reaches of long restarts differ at $`x`$ and at the points of level 2 below it ([SHIFT.md](SHIFT.md) §4); now the tails agree: LT holds at $`x`$ and at every point of level 2, so that property is not a ghost
      ([SHIFT.md](SHIFT.md) §8.4); now the CAND-2 test is not a ghost either, so Conjecture U-TAIL is a theorem, and caps never block the placement (W) of long copies,
      only room can ([SHIFT.md](SHIFT.md) §9.4); now the copying plan needs no anchor copy, so room under ceilings is no obstruction, and far heads have room
      (RE-PLACE, DOUBLE-FAR; [SHIFT2.md](SHIFT2.md) §1.4); now every span below the first index fixed point is placed exactly
      (MIN-EXACT, SPAN-PLACE, RES-ALL\*; [SHIFT2.md](SHIFT2.md) §2.4); left: the deep spans over an uncountable offset (D1b), and the sets that meet $`[x^\#, \nu)`$; the converse in Carlson–Wilken 2012 does not give them ([SHIFT2.md](SHIFT2.md) §3.4), and the present tools reach them only under the open hypothesis LOW ([SHIFT3.md](SHIFT3.md) §1.4), now weakened to $`\nu_C \lt \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$, while LOW itself is
      reduced to a cap for self-crossing restarts ([SHIFT3.md](SHIFT3.md) §2.4); that cap now holds for every code below $`P'`$, so **LOW is false given FRAG** ([SHIFT7.md](SHIFT7.md) §1.1, 1 review; before: at its first test case and for every code below $`G(\hat\zeta_{23})`$, [SHIFT5.md](SHIFT5.md) §1.1, §2.1, [SHIFT6.md](SHIFT6.md) §1.1, §2.1, §3.1, and the reduction of not-LOW to EX$`^w`$ below $`P'`$, [SHIFT6.md](SHIFT6.md) §2.1); reaches now commute with base change below the code $`G_2^2`$ at level 1, and the deep spans whose offset is below $`\omega^{G_2^2}`$ are placed under LOW, but not under the weaker hypothesis (blocking point, [SHIFT5.md](SHIFT5.md) §1.2); now the tools and TC⁺ below $`G_2^2`$ hold at every level, so the weaker hypothesis becomes $`\nu_C \lt \upsilon^\infty`$, but a pin of long prefixes whose atoms are moved is not written (blocking point, [SHIFT5.md](SHIFT5.md) §2.2); now that pin is proved and reaches commute with base change below the code $`\varepsilon_{\hat G+1}`$ at every level; left: LOW$`^\infty`$, exact landing reaches and caps for larger codes, and a larger zone ([SHIFT6.md](SHIFT6.md) §1.2; now TC⁺ holds at the codes of the repaired blocking point too, and $`\nu_C = \nu_S`$ follows from FRAG, LOW$`^\infty`$ and exact reaches, caps and zones for the codes $`\ge G(\hat\zeta_{23})`$, REDUCTION$`^{(6)}`$, [SHIFT7.md](SHIFT7.md) §1.2)
    - A7 relativized patterns of $`R_1^+`$ and uniform assignments between ordinals and patterns (announced by Wilken) —
      proved (RC-PIN, RC, U, UNIF; [PINS.md](PINS.md) §1; the closures are finite, CL-FIN, and are explicit pin patterns, EXPL,
      [BREAK.md](BREAK.md) §4); that the assignments are elementary recursive — outline only
  - **L** lower bound $`\psi_{\Omega_1}(I_\omega) \subseteq \mathrm{Core}(R_2^+)`$ — open
    - L0 in $`R_2^C`$: equivalent to "every $`\gamma \lt \psi_{\Omega_1}(I_\omega)`$ is below some $`\max C^*_n`$" — proved
    - L-CERT below $`\theta_0`$: reductions proved (I-FREE, OE, EPS-RED, FS-OE, RED-BMS, S-RED, MU-A, MU-B, UNIF-V);
      also MU-0 and MU-B0 ((M4) at level 0; adds nothing to the core); left: (M4) at level $`\ge 1`$, (M1)–(M3), and the
      local step below SRO — open (with them the first fan needs an inaccessible, RED-HM, [COVER.md](COVER.md) §5.3); the top step at SRO
      and several uniform families of steps — proved for explicit patterns ([COVER.md](COVER.md) §6.1); all 26 undecided limit jumps of the
      sample above $`V_3`$ — proved ([FANFREE.md](FANFREE.md) §1); the step for every $`n`$ on all 3,166 sample matrices below SRO, IDX-ADD among them, and the property (REP) of the program — proved ([FANFREE.md](FANFREE.md) §7.1, §10.1, [VEBLEN.md](VEBLEN.md) §3, §10, [THETA.md](THETA.md) §3, §9.3, [SHIFT.md](SHIFT.md) §3, §8.3, §9.3, [SHIFT2.md](SHIFT2.md) §1.3, §2.3, §3.3, [SHIFT3.md](SHIFT3.md) §1.3, §2.3, [SHIFT4.md](SHIFT4.md) §1.3, §2.3); native codes up to the
      Bachmann–Howard ordinal, then on all indices below $`\upsilon_1`$ with one level of references, then (each bound $`b`$ from here to $`Z_\omega`$ gives $`\iota(\mathrm{CH}_2) \ge b`$) below $`\Phi_1`$ with nested references and the first blocks, then below $`\Lambda_\Gamma`$ with modules for the fixed points of $`\upsilon`$, then below $`\Lambda_T`$ with nested and decorated blocks (MODULE-RED⁺, CHAIN⁺, IDX-T), then below $`Z_K`$ with nested levels as slots (CHAIN-K, IDX-K), then below $`Z_\Xi`$ with absolute codes (HOST-Γ, IDX-R), then below $`\theta_{\Xi_2}(0)`$ with a collapsing hierarchy over $`\Omega_1`$ and upper nests of $`\le_1`$-atoms (UPPER-HOST, IDX-U), then below $`Z^+`$ with one flat row of $`\le_1`$-items and atom blocks (ROW2, IDX-3), then below $`Z_\omega`$ with nested rows at every level (ROW$`_j`$, IDX-n), and for $`\mathrm{CH}_3`$ a top with one L1p configuration ($`\iota(\mathrm{CH}_3) \ge Z''_\omega`$, HOST$`_k`$, IDX-ω⁺; by RED-TOWER the chain number may grow with the target), then pair blocks for the stages below $`\omega^\omega`$ ($`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$, IDX$`^p`$), then past $`\upsilon^*`$ ($`\iota(\mathrm{CH}_3) \ge Z''_\omega \gt \upsilon^*`$, EN=EX, EMB), then past $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ ($`\iota(\mathrm{CH}_3) \ge Z[0]`$, PSI$`^T`$, EN=EX$`^T`$) — proved ([FANFREE.md](FANFREE.md) §10.2, [VEBLEN.md](VEBLEN.md) §2, §9, [THETA.md](THETA.md) §2, §9.2, [SHIFT.md](SHIFT.md) §2, §8.2, §9.2, [SHIFT2.md](SHIFT2.md) §1.2, §2.2, §3.2, [SHIFT3.md](SHIFT3.md) §1.2, §2.2, [SHIFT4.md](SHIFT4.md) §1.2, §2.4), then up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$ ($`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$, GEN-ALL; [SHIFT5.md](SHIFT5.md) §1.3), then up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$ with decorations as stage regions (SUPPLY-0, DEC-REGION, PUSH$`^{\varepsilon_0}`$; [SHIFT5.md](SHIFT5.md) §2.3), then up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ with stage labels made of whole lower codes (STAGE-TOWER, LADDER; [SHIFT6.md](SHIFT6.md) §1.3), while stage labels of level $`\Omega_1`$ in label-block systems give no gain (SIGMA-BARRIER; [SHIFT6.md](SHIFT6.md) §2.3), then up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$ with the one chain number 3, the labels being points inside the pair of the code (PAIR-DOWN, IDX$`^q`$; [SHIFT6.md](SHIFT6.md) §3.3); stage labels of every finite level and the start of the ω-top would give $`\psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega)`$, once a referee's repair of one blocking point has a second check ([SHIFT7.md](SHIFT7.md) §1.3); the step for all
      matrices below SRO, and a map without matrices on all terms — open (with values without L1p it would give $`\iota(\mathrm{CH}_2) \ge \theta_0`$, [FANFREE.md](FANFREE.md) §7.2)
    - L-CERT on $`[\theta_0, \psi_{\Omega_1}(I_0))`$ and above — open
    - L-BMS through $`\Phi_3`$ — blocked: by DOM₂ a pattern of $`\Phi_3`$ without a chain of length 3 stays below $`m_3`$,
      and the output relation of $`\Phi_3`$ never has such a chain (Theorem A, proved; for the closure, BAR_R, checked)
  - **Side leaves**
    - **DOM₂** — proved, with SHARP; DOM$`_k`$ for every $`k`$ — conjecture
    - locate $`C^*_3`$ — open (Conjecture C3′ in §3, its derivation refuted; known: $`m_3 \ge \Lambda_\varepsilon`$, and the skeleton ends
      below $`m_3`$; the reach-only route fails (NO-PROMOTE); a chain is a fan whose limit is a left end (CF);
      $`c_0, c_1, c_2`$ are limit points of the class $`C_{\omega^\omega}`$, so C3′′ is false (C3-VEB, C3′′-FALSE; [PINS.md](PINS.md) §4,
      [BREAK.md](BREAK.md) §3); limits of levels lie in no pair, and in $`R_2^C`$ the first fan is below $`m_3`$ (LIM-CAP, DOM_F; [BREAK.md](BREAK.md) §6); the first
      fan is above $`T_\omega`$, has two successors and is open in $`R_2^C`$ (FAN-CAP, OPEN-C, LONG-NEST; [BREAK.md](BREAK.md) §7.4); in $`R_2^C`$ the bottoms of
      chains are exactly the points of the core with an infinite closed fan, and the least closed $`n`$-fans stay below $`m_3`$ (CP3, FIN-FAN);
      the least fan is described, with order type $`\omega^2`$ (FS, OF; [COVER.md](COVER.md) §2, §5.2), and $`m_F \gt \nu_C`$ ([COVER.md](COVER.md) §6.4); $`m_F`$ is the limit of the points of one sequence of chains of pairs, and
      $`\sigma_N = m_F`$ ([FANFREE.md](FANFREE.md) §4); $`c_2 \lt \omega_1^{CK}`$)
    - Lean: the order type of the bounded terms is $`\psi_{\Omega_1}(X)`$; Lemma LOC (whether a finite set is
      isominimal depends only on the structure up to its largest element; on paper, not refereed) — open

## 6. Experiments

All checked or conjecture; nothing here is a proof. Each run was under 60 seconds.

**Tools.** A Python port of InaccPsi's comparison, `KLt` and `NF` agrees with Lean's `Term.cmp` on 600 of
600 random pairs and with `NF` on 120 of 120 terms. The trio matrices $`M`$ are read by three programs:
`por/tr3.py` (Wilken's $`\upsilon_\iota`$ and $`T^\tau`$ terms), Ytosk's algorithm (2020, trio matrix →
extended Buchholz $`\psi`$, valid below SRO;
[blog post](https://googology.fandom.com/wiki/User_blog:Ytosk/Algorithm_that_changes_BMS_matrices_into_ordinals_up_to_SRO),
run only), and "BMS analyzer Mk. II" (run only). The pattern of $`M`$ is $`\Phi_3(M)`$ of
`por/phi3def2.py`, and "$`\lt`$" between patterns is shown by certificates of Carlson's rules.

**Table** (the conjectured term $`J`$ of the least realization of $`\Phi_3(M)`$). In the table, `p0(a)` is
$`\psi_{\Omega_1}(a)`$, `p1(a)` is $`\psi_{\Omega_2}(a)`$, `pI0(a)` is $`\psi_{I_0}(a)`$, `W` is $`\Omega_1`$, `W_a` is
$`\Omega_a`$, `w` is $`\omega`$, `w^x` is $`\omega^x`$, `P` is `p1(W_w)`, and `t6` is the term of row 6.
Matrices: `Z` = (0,0,0)(1,1,1), `K` = (1,1,0)(2,2,1). Value status: "proved" = Theorem S below
$`V`$; "FRAG" = Theorem S below $`V_3`$, which uses Lemma FRAG (now proved, so these rows are proved too); "num" =
checked numerically only. Agrees: which
readings convert to the same $`J`$.

| # | name | M | J | value | agrees |
|---|---|---|---|---|---|
| 1 | υ₁ | `Z` | `p0(W_w)` | proved | tr3, Ytosk |
| 2 | υ₂ | `Z K` | `p0(W_w+P)` | proved | tr3, Ytosk |
| 3 | υ_ω | `Z K (2,0,0)` | `p0(W_w+w^(P+1))` | proved | tr3, Ytosk |
| 4 | U = υ_{ω+1} | `Z K (2,0,0) K` | `p0(W_w+w^(P+1)+P)` | proved | tr3, Ytosk |
| 5 | V₂ = υ_{ω·2+1} | `Z K (2,0,0) K (2,0,0) K` | `p0(W_w+w^(P+1)·2+P)` | proved | tr3, Ytosk |
| 6 | V = υ_{ω²} | `Z K (2,0,0)(2,0,0)` | `p0(W_w+w^(P+2))` | FRAG | tr3, Ytosk |
| 7 | V+1 | `V (1,0,0)` | `w^(t6+1)` | FRAG | tr3 |
| 8 | ε after V | `V (1,1,0)` | `phi(1,t6+1)` | FRAG | tr3 |
| 9 | φ₂ after V | `V (1,1,0)(2,1,0)` | `phi(2,t6+1)` | FRAG | tr3 |
| 10 | BHO after V | `V (1,1,0)(2,2,0)` | `p0(W_w+w^(P+2)+phi(1,W+1))` | FRAG | tr3 |
| 11 | υ_{ω²+1} | `Z K (2,0,0)(2,0,0) K` | `p0(W_w+w^(P+2)+P)` | FRAG | tr3, Ytosk |
| 12 | υ_{ω²+ω} | `Z K (2,0,0)(2,0,0) K (2,0,0)` | `p0(W_w+w^(P+2)+w^(P+1))` | FRAG | tr3, Ytosk |
| 13 | υ_{ω²+ω+1} | `Z K (2,0,0)(2,0,0) K (2,0,0) K` | `p0(W_w+w^(P+2)+w^(P+1)+P)` | FRAG | tr3, Ytosk |
| 14 | υ_{ω²·2} | `Z K (2,0,0)(2,0,0) K (2,0,0)(2,0,0)` | `p0(W_w+w^(P+2)·2)` | FRAG | tr3, Ytosk |
| 15 | V₃ = υ_{ω³} | `Z K (2,0,0)(2,0,0)(2,0,0)` | `p0(W_w+w^(P+3))` | num | tr3, Ytosk |
| 16 | υ_{ω³+1} | `V₃ K` | `p0(W_w+w^(P+3)+P)` | num | tr3, Ytosk |
| 17 | υ_{ω⁴} | `Z K (2,0,0)(2,0,0)(2,0,0)(2,0,0)` | `p0(W_w+w^(P+4))` | num | tr3, Ytosk |
| 18 | υ_{ω^ω} | `Z K (2,0,0)(3,0,0)` | `p0(W_w+w^(P+w))` | num | tr3, Ytosk |
| 19 | BHO after row 18 | `Z K (2,0,0)(3,0,0)(1,1,0)(2,2,0)` | `p0(W_w+w^(P+w)+phi(1,W+1))` | num | tr3 |
| 20 | υ_{ω^ω+1} | `Z K (2,0,0)(3,0,0) K` | `p0(W_w+w^(P+w)+P)` | num | tr3, Ytosk |
| 21 | υ_{ω^ω^ω} | `Z K (2,0,0)(3,0,0)(4,0,0)` | `p0(W_w+w^(P+w^w))` | num | tr3, Ytosk |
| 22 | υ_{ε₀} | `Z K (2,0,0)(3,1,0)` | `p0(W_w+w^(P+eps0))` | num | tr3, Ytosk |
| 23 | υ_{ε₀+1} | `Z K (2,0,0)(3,1,0) K` | `p0(W_w+w^(P+eps0)+P)` | num | tr3, Ytosk |
| 24 | υ at BHO | `Z K (2,0,0)(3,1,0)(4,2,0)` | `p0(W_w+w^(P+p0(phi(1,W+1))))` | num | tr3, Ytosk |
| 25 | υ at υ₁ | `Z K (2,0,0)(3,1,1)` | `p0(W_w+w^(P+p0(W_w)))` | num | tr3, Ytosk |
| 26 | first fixed point of υ | `Z K (2,1,0)` | `p0(W_w+w^(P+W))` | num | Ytosk |
| 27 | | `Z (1,1,1)` | `p0(W_w·2)` | num | Ytosk |
| 28 | | `Z (2,0,0)` | `p0(w^(W_w+1))` | num | Ytosk |
| 29 | | `Z (2,1,0)` | `p0(w^(W_w+W))` | num | Ytosk |
| 30 | | `Z (2,1,0)(3,2,0)` | `p0(phi(1,W_w+1))` | num | Ytosk |
| 31 | | `Z (2,1,0)(3,2,1)` | `p0(W_(w·2))` | num | Ytosk |
| 32 | | `Z (2,1,1)` | `p0(W_(w^2))` | num | Ytosk |
| 33 | | `Z (2,1,1)(3,0,0)` | `p0(W_(w^w))` | num | Ytosk |
| 34 | | `Z (2,1,1)(3,1,0)` | `p0(W_W)` | num | Ytosk |
| 35 | | `Z (2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)` | `p0(W_(W_W))` | num | Ytosk |
| 36 | SRO | `Z (2,1,1)(3,1,0)(2,0,0)` | `p0(pI0(0))` | num | none |

Here BHO is the Bachmann–Howard ordinal, and `phi(1,W+1)` is $`\varepsilon_{\Omega_1+1}`$. In rows 1–6, 11–18 and
20–23 the name is $`\upsilon_{1+\eta}`$ with $`\eta \lt \Gamma_0`$, so "name = $`J`$" is proved there by Theorem T; rows 24–26
have $`\eta \ge \Gamma_0`$; the term of row 26 is now proved to be $`\Xi_1`$ (Theorem T++, [REACHES.md](REACHES.md) §2). The column
"value" says whether the point of $`\Phi_3(M)`$ is that name.

Checked on this table:

- all 36 terms $`J`$ are normal forms and strictly increasing, in Python and in Lean;
- 67 of 67 certificates were found and replayed: $`\Phi_3`$ of row $`i`$ is below $`\Phi_3`$ of row $`i+1`$ for all 35
  neighbour pairs; $`\Phi_3(M[2]) \lt \Phi_3(M)`$ for the 31 rows from $`V`$ on ($`M[n]`$ is the $`n`$-th term of the
  fundamental sequence); $`\Phi_3(\mathrm{SRO}[1]) \lt \Phi_3(\mathrm{SRO}[2])`$;
- tr3 gives the same $`J`$ on the 25 rows it names, Ytosk on 30 rows; no reading disagrees.

**Checks of 2026-10** (each run under 60 seconds; certificates count only when replayed).

- **The map $`B`$ of STEP.** Implemented next to the Python port of InaccPsi together with the system of
  Weiermann–Wilken 2011. On 7 random samples (up to 12,720 pairs each, up to 5 levels) $`B`$ had 0 order errors,
  every image was a normal form, and every level-0 image was below $`\psi_{\Omega_1}(A + \theta)`$. Two broken
  variants of $`B`$ fail the same test (68 order errors; 44 non-normal forms). The referee's exhaustive test
  (all small terms): for STEP-0 up to 3,554 terms and 6.3 million pairs, 0 problems; for $`A = \Omega_\omega + \theta`$
  only tiny sets (61 and 35 terms), 0 problems.
- **The map $`E`$ of LOW-STEP.** 8 random runs ($`\eta = 0, 1, 2`$, up to 5 levels, about 0.4–0.5 million pairs each)
  and 7 runs on all small terms (up to 8.76 million pairs): 0 order errors, every image in the domain. The
  referee's own 12 runs ($`\eta`$ up to $`\omega^2`$, larger $`\sigma`$, an $`\varepsilon`$-number $`\sigma`$ that is not strongly
  critical, up to 6 levels; 770,000–829,000 pairs each): 0 errors. Broken variants (no $`F`$, no $`\Omega^2`$ prefix,
  swapped $`\varphi`$ arguments) fail.
- **Second review of $`B`$.** Own code; 14 random runs (1,117,200 pairs) and 7 exhaustive runs (11,197,771 pairs),
  with $`A = A_0, A_1, A_{\omega+1}, A_{\omega^2}`$: 0 order errors, 0 non-normal images, 0 bound errors.
- **Lemma FOLD.** The minimum of a covering and the identity was a covering in 9,000 of 9,000 random cases in
  $`R_1^+`$ below $`\varepsilon_0`$; the control map (the maximum) failed 20 times. The leading-term map was a closed
  embedding below the given map, keeping $`\le_1`$ forward, in 9,522 of 9,522 random cases.
- **The map $`\mu`$ of MU-A.** Standard on all 3,913 generated terms of $`G_A`$; the referee's own copy, written from the
  definition only, gave 0 order errors on 47,990 pairs of random $`G_A`$ terms (up to 995 columns). Of the 36 table
  rows, 19 lie in $`G_A`$, and $`\mu`$ gives their matrices.
- **Certificates toward the lower bound** (all 2,511 found certificates replayed):

  | set | certified | undecided |
  |---|---|---|
  | 1,423 single-root standard matrices below SRO with at most 7 columns whose reading is a term; neighbour pairs | 1,389 of 1,422 | 33 |
  | terms of $`G_A`$ with at most 10 columns; neighbour pairs | 478 of 496 | 18 |
  | fundamental-sequence steps at 329 limits | 648 of 658 | 10 |
  | reversed neighbour pairs (control) | 0 of 24 | — |

  No undecided pair was refuted. All 26 known order failures of $`\Phi_3`$ (58 pairs) lie above SRO.
- **The map $`\mu_B`$ of MU-B.** 17,736 random terms of $`G_B`$ and the referee's 104,071 structured terms: 0 order errors,
  all below SRO, all images standard (yaBMS). Certificates: of 300 neighbour pairs of a random sample of $`G_B`$
  (at most 10 columns), 271 certified and replayed, 29 undecided, none refuted; 30 reversed pairs: 0.
- **Chains below $`m_3`$** (2026-10). 6 certificates "point of the pattern $`\lt m_3`$", replayed, among them
  $`\Phi_3(\mathrm{SRO})`$ and $`\Phi_3((0,0,0)(1,1,1)(2,2,2)(3,3,3))`$; the referee added patterns with 2, 3, 4 separate
  chains of length 2. No certificate for the reverse order within 45 seconds.
- **DOM₂.** Certificates were found for the predicted order "pattern without a chain of length 3 below
  $`m_3`$" on 4 shapes, and none, within 40 seconds each, for the 3 reverse directions. Longest chain of
  $`\Phi_3(M)`$: 2, on 3,875 matrices from $`(0,0,0)(1,1,1)(2,2,2)(3,3,3)`$ (rows $`\le 3`$, $`\le 24`$ columns).
- **The base map $`\mu_0`$ (MU-B0).** 6,480 random terms of $`G_{B0}`$, each sample with a random order-preserving map on the
  base: 0 order errors, 0 non-standard images (yaBMS), all below SRO. With a shuffled base map the same sample gives
  111 order errors and 182 non-standard images, so the test can fail. The referee's new sample (400 terms): 0 errors.
- **The local step above $`V_3`$.** 160 neighbour pairs of images of $`G_{B0}`$ (at most 10 columns): 134 certified and
  replayed (again by the referee), 26 undecided (all at limits whose last columns come from a base term), none
  refuted; 30 reversed pairs: 0. Now 5 of the 26 have replayed certificates, one more is proved by hand, and 20 stay
  undecided ([COVER.md](COVER.md) §6.1). Now all 26 are proved by hand, and the hand proofs replay as certificates ([FANFREE.md](FANFREE.md) §1). For $`V_3`$ itself: 11 of 11 certificates for $`N \le 10`$, replayed.
- **Chains of $`\Phi_3`$.** Theorem A, BAR, BAR_R, "closure = output relation" and "longest chain of the closure is 2":
  0 failures on 12,963 matrices from six starts (78,991 nested pairs). The referee: Theorem A had 0 failures on 229,888
  random inputs; BAR_R failed on 824 of them (a re-run: 664), and none of those is standard.

**The first inaccessible.** Enumerating all 1,650,729 normal forms of size at most 9: the least countable
term that contains any $`I`$-symbol is $`\psi_{\Omega_1}(\psi_{I_0}(0))`$, and every countable term without one
is below it (checked; now proved for all terms by Lemma I-FREE). Conjecture: the first pattern that needs $`I_0`$ is $`\Phi_3(\mathrm{SRO})`$, with
$`\mathrm{SRO} = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)`$, and its point is $`\psi_{\Omega_1}(\psi_{I_0}(0))`$. Evidence:
$`\mathrm{SRO}[n]`$ reads as $`\psi_{\Omega_1}`$ of an $`\Omega`$-tower of height $`n+2`$; certificates give
$`\Phi_3(\mathrm{SRO}[n]) \lt \Phi_3(\mathrm{SRO})`$ for $`n = 2, 3`$; $`n = 4`$ timed out. Where $`I_1`$ is first needed is
open.

**Chains against $`\Phi_3`$.** For 14 matrices from $`V_3`$ up to $`(0,0,0)(1,1,1)(2,2,2)(3,3,0)`$, the
pattern $`\Phi_3(M)`$ has $`\le_2`$-chains of length at most 2 (checked; also on the 3,875 matrices above). By DOM₂
(proved), the point of every such pattern is below $`m_3 \lt \min C^*_3`$; the 8 certificates of the earlier run are
no longer needed. If Conjecture CH holds, an order preserving $`\Phi_3`$ must use chains of length 3 or more past the
first inaccessible; with only chains of length 2 it cannot reach $`\psi_{\Omega_1}(I_\omega)`$. This consequence is
**not proved**: the output relation of $`\Phi_3`$ has no chain of length 3 (Theorem A, proved), but the bound by $`m_3`$ also
needs "$`\Phi_3(M)`$ is a pattern" (open), and it is about $`R_2^C`$ only.

## 7. Files

| file | what it proves |
|---|---|
| [CountSeg.lean](CountSeg.lean) | Lemma L, `bounded_inter_Om1`, `vals_inter_Om1`, `three_bounds` |
| [LowSeg.lean](LowSeg.lean) | Lemma IS and Lemma CONT |
| [ConjT.lean](ConjT.lean) | the InaccPsi side of Theorem T-UP: (HA) for $`A_\eta`$, the induction to $`\eta = \omega^2`$ with STEP as a hypothesis, Conjecture U from it, and the arithmetic of Lemma M |
| [LowerT.lean](LowerT.lean) | the InaccPsi side of Theorem T-LOW: the induction to $`\eta = \omega^2`$ with LOW-0 and LOW-STEP as hypotheses, and Theorem T from both halves |
| [LowTerms.lean](LowTerms.lean) | the seven terms $`u(\eta)`$ of §4: normal forms, values, order, and $`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ |

Nothing about $`R_2^+`$ itself is in Lean. The results above $`\upsilon_{\omega^3}`$ are on the second page
[RESTARTS.md](RESTARTS.md), those above $`\Xi_\omega`$ on the third page [REACHES.md](REACHES.md), those beyond $`\Lambda_\varepsilon`$ on
the fourth page [PINS.md](PINS.md), and those where the skeleton ends, with the levels above it, on the fifth page [BREAK.md](BREAK.md), and the
results by covering minimality and the level-0 description (the fifth to seventh rounds) on the sixth page [COVER.md](COVER.md), and the eighth to tenth rounds on the seventh page [FANFREE.md](FANFREE.md), and the eleventh and twelfth on the eighth page [VEBLEN.md](VEBLEN.md), and the thirteenth and fourteenth on the ninth page [THETA.md](THETA.md) (with the summary of the earlier rounds and the results on $`R_2^S`$ against $`R_2^C`$, moved there from this page), and the fifteenth to seventeenth on the tenth page [SHIFT.md](SHIFT.md), and the eighteenth to twentieth on the eleventh page [SHIFT2.md](SHIFT2.md), and the twenty-first and twenty-second on the twelfth page [SHIFT3.md](SHIFT3.md), and the twenty-third and twenty-fourth on the thirteenth page [SHIFT4.md](SHIFT4.md), and the twenty-fifth and twenty-sixth on the fourteenth page [SHIFT5.md](SHIFT5.md), and the twenty-seventh to twenty-ninth on the fifteenth page [SHIFT6.md](SHIFT6.md), and the thirtieth on the sixteenth page [SHIFT7.md](SHIFT7.md); some results of the first round are on [ROUND1.md](ROUND1.md), and older details moved from this page are on [ROUND2.md](ROUND2.md).

## 8. References

- T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001).
- T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009).
- T. J. Carlson, G. Wilken, "Normal forms for elementary patterns", JSL 77 (2012).
- T. J. Carlson, G. Wilken, "Tracking chains of Σ₂-elementarity", APAL 163 (2012), https://www.sciencedirect.com/science/article/pii/S0168007211001199.
- G. Wilken, "Pure patterns of order 2", https://arxiv.org/abs/1608.08421.
- G. Wilken, "Tracking chains revisited", https://arxiv.org/abs/1611.04348.
- G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
- G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
- A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined θ-functions", MLQ 57 (2011).
- G. Wilken, "A glimpse of Σ₃-elementarity" (2020).
- G. Wilken, "Pure Σ₂-elementarity beyond the core", APAL 172 (2021).
- W. Buchholz, "A new system of proof-theoretic ordinal functions", APAL 32 (1986).
- W. Buchholz, "A simplified version of local predicativity" (1992).
- W. Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof Theory (1998), Ch. IV.
