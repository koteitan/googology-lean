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
$`\alpha`$-th fixed point of $`\iota \mapsto \upsilon_\iota`$ (§3, [RESTARTS.md](RESTARTS.md) and [REACHES.md](REACHES.md)), and now up to
$`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$ ([PINS.md](PINS.md) §3). The core half alone is proved in $`R_2^C`$ further, on
$`[0, \nu_C]`$, where $`\nu_C \gt \nu_P`$ is the first point where $`R_2^C`$ stops being skeletal ([BREAK.md](BREAK.md) §2).

## 3. What is proved

**Summary.** Below $`\upsilon_{\omega\cdot\omega}`$ the claim holds, in both $`R_2^C`$ and $`R_2^S`$: every ordinal
below $`\upsilon_{\omega\cdot\omega}`$ is in the core, and it is the countable value of an InaccPsi normal form whose
collapse arguments are below $`I_\omega`$ (Theorem LOW below). Wilken's points have exact names:
$`\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ for $`\eta \lt \Gamma_0`$ (Theorem T, §4), and now for every
$`\eta`$ below the first fixed point $`\Xi_1`$ of $`\iota \mapsto \upsilon_\iota`$ (Theorem T+). Lemma FRAG is now proved. These results of
2026-10 (FRAG, FRAG2, the restart blocks, T+) are on the second page [RESTARTS.md](RESTARTS.md). The third page
[REACHES.md](REACHES.md) has the newest ones: the exact reach of every restart up to $`\Lambda_\varepsilon`$ (some results with
2 reviews), the names $`\Xi_\alpha = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot\alpha)`$ (2 reviews), so that in $`R_2^C`$ the claim
holds up to $`\Phi_1`$, the structure of $`R_2^S`$ on the whole skeletal regime, where the skeleton ends, and the least chain
of length 3. The fourth page [PINS.md](PINS.md) has the results of the next round: relativized patterns of $`R_1^+`$
(Wilken's announced relativized core, rebuilt except "elementary recursive"), the exact reaches up to $`\Theta_A`$, the names
$`\upsilon_{1+\iota(\eta)} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ of all $`\upsilon`$-points (Theorem GEN), so that in $`R_2^C`$ the claim holds up
to $`\Lambda_\varepsilon`$, and the shape of the bottom of a chain of length 3. It also records a gap found in Lemma LEFT. The fifth
page [BREAK.md](BREAK.md) has the latest two rounds: INC1, NOBAD and Lemma LEFT proved with no hypothesis left, the first
non-skeletal point of $`R_2^S`$ found exactly, that of $`R_2^C`$ equal to it unless one extra pair exists, the first block of every
level of nested pairs, limits of these levels never in a pair, chains of length 3 as fans whose limit is a left end (so the
shape C3′′ is false), the finiteness of the closures $`C_\tau(z)`$, and the core of $`R_2^C`$ up to $`\nu_C \gt \nu_P`$. Its §7 has the third round:
every block of every level of nested pairs below their limit $`T_\omega`$ has the shape of the first block (Theorem SH), every fan apex
lies above $`T_\omega`$ (2 reviews), the least fan has exactly two successors and in $`R_2^C`$ is open, the question $`\nu_C = \nu_S`$ is a
question about $`R_2^S`$ alone, and the name of $`\nu`$ and the base changes between gaps are reduced to the index statement $`o_2 = \omega`$ and
two more. Its §8 has the fourth round: in $`R_2^C`$, every level of nested pairs has exactly $`\omega`$ points below its left end
($`o_k = \omega`$ for every $`k`$, Theorem O$`^C`$, 1 review, by Carlson's minimality against coverings), so the shape part of NU-NAME holds in
$`R_2^C`$; in $`R_2^S`$, $`o_2 = \omega`$, NOLIM above $`\nu_P`$ and $`\nu_C = \nu_S`$ stay open, $`\nu_C = \nu_S`$ now implies $`o_2 = \omega`$, and NOLIM is reduced
to one statement per gap. The sixth page [COVER.md](COVER.md) has the fifth round, all by the same minimality (1 review each): in
$`R_2^C`$, a point of the core is the bottom of a chain of length 3 iff it has an infinite $`\le_1`$-chain of right ends (Theorem CP3), the
least fan is described except its order type, and NOLIM holds; in $`R_2^S`$, $`\nu_C = \nu_S`$ is equivalent to NOLIM and
$`o_2 = \omega`$ there, and $`o_k = \omega`$ is reduced to an $`R_2^S`$ form of Carlson's minimality and one pinning statement. Its §5 has the sixth
round (1 review each): the level-0 description of $`R_2^S`$ holds at every countable ordinal (so SKEL⁺, SKEL$`^\omega`$ and RIGHT in $`R_2^S`$ are
proved, and the results that used them, NOLIM in $`R_2^C`$ among them, move from outline to proof level); the least fan of $`R_2^C`$ has
order type $`\omega^2`$; whether it needs an inaccessible is exactly a lower bound for fan-free patterns whose right ends have no reach;
and the $`R_2^S`$ form of Carlson's minimality holds up to $`\beta_0`$. $`C^*_3`$ lies below $`\omega_1^{CK}`$ (Carlson 2009, Thm 15.2), but it still has
no upper bound by an InaccPsi term and no name. Above $`\Lambda_\varepsilon`$ both
halves are open in $`R_2^C`$ (the core part is proved up to $`\nu_C`$), and above $`\upsilon_{\omega^3}`$ in $`R_2^S`$.

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
$`[0, \rho_{\Theta_A+\omega^2})`$ ([PINS.md](PINS.md) §2), and to $`[0, \rho_{\Theta_{d\omega}})`$, and to $`[0, \nu_C]`$ with $`\nu_C \gt \nu_P`$ ([BREAK.md](BREAK.md) §2, §4).

- **Lemma PT** (1 review). Let $`Q`$ be a pattern in the full sense of Carlson 2009, Def 5.6. If every copy of $`Q`$ in
  $`R_2^C`$ puts the point of $`Q`$ at $`\ge v`$, then $`[0, v] \subseteq \mathrm{Core}(R_2^C)`$ (Carlson 2009, Lemma 15.11,
  Thms 14.10, 14.14). Only a lower bound for one pattern is needed, no order statement.
- **Theorem CORE-C3** (1 review). Every ordinal $`\le \upsilon_{\omega^3} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+3})`$ is in
  $`\mathrm{Core}(R_2^C)`$. Before, this was known only given FRAG. Proof: the caps of Theorem EQB′′ of
  [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md), block by block, use no FRAG; they show that no $`\alpha \lt \upsilon_{\omega^3}`$ is
  $`\le_1`$ to everything above it; then Carlson 2009, Thm 14.14. One step of the caps (a $`\Pi_2`$ transfer whose formula
  also held $`\le_1`$-facts between two old parameters) was incomplete; the repair, Lemma DIAG′ (leave those facts out:
  they hold already), is proved. The end point: every copy of $`\Phi_3(V_3)`$ puts its point at $`\ge \upsilon_{\omega^3}`$
  (by the caps and Lemma TOP; the referee gave this short proof), then Lemma PT. The name is Theorem T with
  $`\eta = \omega^3`$. With Lemma IS: below $`\upsilon_{\omega^3}`$ the core of $`R_2^C`$ and the countable term values are both
  all of $`[0, \upsilon_{\omega^3})`$. Minor points of the review: one choice of $`\tau`$ in Wilken 2007
  (APAL 145, 162–175), Claim 5.5(b), is still not written out; Lemma PT needs $`Q`$ to be a pattern (checked for the
  patterns used).
- **Corollary** (1 review). $`m_3 \ge \upsilon_{\omega^3}`$ and $`\min C^*_3 \ge \upsilon_{\omega^3}`$, without FRAG ($`m_3`$ is defined
  under "Chains" below).

**$`R_2^S`$ against $`R_2^C`$** (2026-10). Let $`\beta_0`$ be the least stage $`\beta`$ at which some relation
$`\alpha \le_i \beta`$ differs between the two structures ($`\beta_0 = \infty`$ if they are equal). Let
$`\kappa_X = \min\{\kappa : \kappa \le_1^X \beta \text{ for all } \beta \ge \kappa\}`$.

- **Lemma STAGE.** If the structures agree on all pairs below $`\beta`$, then $`\alpha \le_1^S \beta \Rightarrow \alpha \le_1^C \beta`$;
  if also $`\le_1`$ to $`\beta`$ agrees, then $`\alpha \le_2^S \beta \Rightarrow \alpha \le_2^C \beta`$. Tools: the finite-set test
  (T1 below), the leading-term map of Theorem EQ, an $`R_2^+`$ form of Wilken 2021, Lemma 1.7(2), and transfer of
  $`\Pi_2`$ sentences.
- **Corollary FIRST.** Every $`R_2^S`$ relation ($`\le_1`$ or $`\le_2`$) with right end at most $`\beta_0`$ holds in
  $`R_2^C`$ (the case "$`\le_2`$ with right end $`\beta_0`$" was added in a second paper, 2026-10, 1 review). At $`\beta_0`$ the difference is an extra relation of $`R_2^C`$. So
  $`R_2^S = R_2^C`$ if and only if the converse ($`C \Rightarrow S`$) holds at every stage of agreement. Also
  $`\beta_0 \ge \upsilon_{\omega^3}`$ (with FRAG, now proved; now $`\beta_0 \ge \Lambda_\varepsilon`$ and $`\beta_0 \ge \rho_{\Theta_P}`$,
  [REACHES.md](REACHES.md) §1–2; then $`\beta_0 \ge \rho_{\Theta_A}`$, [PINS.md](PINS.md) §2; then $`\beta_0 \ge \rho_{\Theta_A+\omega^2}`$, [BREAK.md](BREAK.md) §4; now $`\beta_0 \ge \nu_C \gt \nu_P`$, §2), and $`\beta_0`$ is countable or $`\infty`$.
- **Theorem LOC** (2026-10, 1 review; [BREAK.md](BREAK.md) §7.3). $`\beta_0`$ is the least stage at which Carlson's covering condition,
  evaluated inside $`R_2^S`$, differs from $`R_2^S`$. So whether $`\nu_C = \nu_S`$ (no "ghost") is a question about $`R_2^S`$ alone. Now
  $`\nu_C = \nu_S`$ implies $`o_2 = \omega`$ in $`R_2^S`$, and given NOLIM the two are equivalent ([BREAK.md](BREAK.md) §8.1, 1 review). Now $`\nu_C = \nu_S`$ iff NOLIM and $`o_2 = \omega`$ hold in $`R_2^S`$
  (GHOST-EQ), and NOLIM holds in $`R_2^C`$ (Theorem NOLIM$`^C`$) ([COVER.md](COVER.md) §3 and §5.1, 1 review).
- **Lemma UPG.** At a stage of agreement, $`\alpha \le_1^C \beta \Rightarrow \alpha \le_1^S \beta`$ when every $`\gamma \lt \alpha`$ lies in an
  isominimal subset of $`\alpha`$ in $`R_2^C`$ (true for $`\alpha = \kappa_C`$ and $`\alpha = \upsilon_{\omega\cdot\omega}`$).
- **KAPPA and CORE-EQ.** $`\kappa_C \le \beta_0 \Rightarrow \kappa_C \le \kappa_S`$, and $`\kappa_S \le \beta_0 \Rightarrow \kappa_S \le \kappa_C`$. So if
  $`\max(\kappa_S, \kappa_C) \le \beta_0`$ (call this AGR), then $`\mathrm{Core}(R_2^S) = \mathrm{Core}(R_2^C)`$. The claim for
  $`R_2^C`$ together with AGR gives the claim for $`R_2^S`$.
- **The converse $`C \Rightarrow S`$ at a stage of agreement** (2026-10, 1 review). Write $`G_C`$ for the set of $`\alpha`$ such
  that every $`\gamma \lt \alpha`$ lies in an isominimal subset of $`\alpha`$. For $`\le_1`$:
  $`\alpha \le_1^C \beta \Rightarrow \alpha \le_1^S \beta`$ holds when $`\beta \lt \kappa_C`$ (**CORE-1**, for every $`\alpha`$; proof by
  Carlson 2009, Def 9.1, Lemma 9.3 and Thm 14.11), when $`\beta`$ is a limit (LIM1), and when $`\beta = \alpha + 1`$
  (ONE-POINT). For $`\le_2`$: a successor stage has no $`\le_2`$ relation in either structure (SUCC2), and the
  converse holds when $`\beta`$ is a limit of its $`\le_1`$-predecessors (LIM2).
- **DICH** (2026-10, 1 review). If $`\beta_0 \lt \infty`$, exactly one case holds. (i) $`\beta_0 = \beta' + 1 \gt \kappa_C`$, and
  the difference is an extra $`\alpha \le_1^C \beta_0`$ with $`\alpha \lt \beta'`$, $`\alpha \notin G_C`$. (ii) $`\beta_0 = \omega^\lambda`$ with $`\lambda`$
  a limit, $`\le_1`$ to $`\beta_0`$ agrees, and the difference is an extra $`\alpha \le_2^C \beta_0`$; the
  $`\le_1`$-predecessors of $`\beta_0`$ have a largest one $`d \lt \beta_0`$, and $`\alpha \le_2 d`$. So below $`\kappa_C`$ the two
  structures can first differ only by a $`\le_2`$ relation of type (ii).
- **R-INC** (2026-10, 1 review). Write W(C) for the claim in $`R_2^C`$, Σ2-GAP for "no extra $`\le_2^C`$ relation of
  type (ii) at a stage $`\le \kappa_C`$" (the referee notes it is equivalent to $`\kappa_C \le \beta_0`$), and INC for
  "$`\le_i^S \subseteq \le_i^C`$ everywhere". Then W(C), Σ2-GAP and INC give AGR, and so
  $`\mathrm{Core}(R_2^S) = \mathrm{Core}(R_2^C) = \rho`$.
- **Stages of type (ii)** (2026-10, 1 review). Such a stage is a $`\beta = \omega^\lambda`$ ($`\lambda`$ a limit) where the
  structures agree on all pairs below $`\beta`$ and on $`\le_1`$ to $`\beta`$, and the $`\le_1`$-predecessors of $`\beta`$ are
  nonempty and bounded, with largest one $`d`$. Let $`D_2 = \{\gamma \lt \beta : \gamma \le_2^C \beta\}`$.
  - **MAX2.** If $`D_2 \ne \emptyset`$, it has a largest element $`a^* \le d`$, and the $`\le_2`$ converse at $`\beta`$ holds for all of
    $`D_2`$ iff $`a^* \le_2^S \beta`$. If $`\beta_0`$ is of type (ii), its extra relation can be taken to be $`(a^*, \beta_0)`$.
  - **RED-d.** $`a^* \le_2^S \beta`$ iff $`\Pi_2`$-UP($`\beta`$): every $`\Pi_2`$ sentence with parameters $`\lt a^*`$ that is true in
    $`R|d`$ is true in $`R|\beta`$. Only witnesses that meet $`[d, \beta)`$ need work. **LOW-Y**: the test T2 holds for every
    $`Y \subseteq [\alpha, d)`$.
  - **FIRST2.** The first $`\lt_2`$-pair $`(\upsilon_\omega, \upsilon_{\omega+1})`$ is a stage of type (ii) with $`a^* = d = \upsilon_\omega`$. The
    referee added (proved): $`a^* = d`$ at every stage of type (ii) below $`\upsilon_{\omega^2}`$, so RED-d reduces nothing at
    the stages where $`R_2`$ is known.
  - **UPCOPY.** Inside the core: let $`P`$ be isominimal with $`a \lt_2 b`$ in $`P`$, and $`Y^\circ = P \cap [a, b)`$. Every
    extension "at $`a`$" (Carlson 2009, Def 8.6) of the downward copy of $`Y^\circ`$ appears below $`b`$ over some upward copy
    of $`Y^\circ`$. That copy lies above all of $`P \cap b`$; it is not $`Y^\circ`$ itself.
  - **EQ-E.** These are equivalent: (E) $`\kappa_C \le \beta_0`$; Σ2-GAP; $`\Pi_2`$-UP($`\beta`$) at every stage $`\beta \lt \kappa_C`$
    of type (ii); **Conjecture CORE-2** (inside the core, at a stage of agreement, $`\le_2^C`$ gives
    $`\Sigma_2`$-elementarity; the order-2 analogue of Carlson 2001, Lemma 5.7(4); Carlson 2009, p. 97, says the
    equivalence "will be established elsewhere").
  - **R-OM.** (R) "$`\kappa_C \le_1^S \gamma`$ for all $`\gamma \ge \kappa_C`$" iff $`\kappa_C \le_1^S \Omega_1`$ (this uses
    $`\kappa_C \le \Omega_1`$, from HULL). Under (E) it holds for every $`\gamma \in [\kappa_C, \beta_0]`$.
  - **AGR iff (E) and (R).** W(C) is not needed for AGR, only for "$`= \rho`$".
  - Open: **PIN** (move the extension from the upward copy back onto $`Y^\circ`$) and **LOW** (extensions with a new
    point $`\le \max X`$, or whose least new point is not additive principal). Only "PIN and LOW give CORE-2" is shown.

**Finite-set tests in $`R_2^S`$** (2026-10). The language $`\{0, +, \le, \le_1, \le_2\}`$ is read as a finite relational one.

- **T1** ($`\Sigma_1`$). $`\alpha \le_1 \beta`$ iff for all finite $`X \subset \alpha`$ and $`Y \subset [\alpha, \beta)`$ there is
  $`\tilde Y \subset \alpha`$ with $`X \lt \tilde Y`$ and an isomorphism $`X \cup \tilde Y \cong X \cup Y`$ that fixes $`X`$;
  $`\tilde Y`$ can be taken above any $`\rho \lt \alpha`$.
- **Lemma PR.** $`\alpha \lt_1 \beta`$ gives $`\alpha = \omega^a`$ with $`a`$ a limit; $`\alpha \lt_2 \beta`$ gives $`\beta = \omega^\lambda`$ with
  $`\lambda`$ a limit, and $`\alpha`$ the supremum of its $`\lt_1`$-predecessors.
- **T2** ($`\Sigma_2`$, graded form; an "iff", while Wilken 2021, Prop 1.6, and Wilken 2020, Prop 21.11, state only
  "if"). $`\alpha \le_2 \beta`$ iff for all such $`X, Y`$ and every $`k`$ there is a copy $`\tilde Y`$ as in T1 such that every
  extension by at most $`k`$ points below $`\alpha`$ extends the isomorphism into $`\beta`$. The copy can also be taken
  cofinal, with $`y \le_1 \beta \Leftrightarrow \tilde y \le_1 \alpha`$, and closed when $`X \cup Y`$ is closed.
- **Theorem CMP.** $`\alpha \le_i^S \beta`$ implies Carlson's covering condition for $`\le_i`$ ($`i = 1, 2`$), computed inside
  $`R_2^S`$. Carlson 2009, p. 98, announces this without proof. Lemma KEEP: the leading-term map keeps forward
  $`\le_1`$ and $`\le_2`$, because both ends of a $`\lt_2`$-pair are additive principal.

**Chains.** A chain of length $`n`$ is $`n`$ additive principal numbers that are pairwise $`\le_2`$. $`C^*_n`$ is the
pointwise least one.

- **Theorem CC** (in $`R_2^C`$). $`\mathrm{Core}(R_2^C) = \sup_n \max C^*_n`$, and a pattern with $`n`$ additive principal
  numbers has its least realization below $`\max C^*_{n+1}`$. (For $`R_2^S`$ this is open; AGR gives the same core.)
- **Theorem DOM₂** (2026-10, $`R_2^C`$). Let $`C^*_3 = \{c_0 \lt c_1 \lt c_2\}`$ and $`m_3 = \min\{m : m \le_1 c_0\}`$. A pattern
  with no chain of length 3 has its least realization below $`m_3`$, and $`m_3 \lt c_0`$. **Theorem SHARP**: the union of
  the isominimal sets with no chain of length 3 is exactly $`[0, m_3)`$. **DOM₁′**, the same for patterns without
  $`\lt_2`$-pairs: their union is $`[0, m_2)`$, with $`m_2`$ the least $`\le_1`$-predecessor of $`\min C^*_2 = \upsilon_\omega`$,
  and $`m_2 = \upsilon_1`$ given the cited core of $`R_1^+`$ and Theorems A, EQ.
- Facts on $`C^*_3`$ (2026-10): no chain of length 3 lies inside $`[0, c_2)`$; $`c_0`$ is a limit of its
  $`\lt_1`$-predecessors; $`m_3 \gt \Xi_\omega`$ and $`c_0 \ge \upsilon_{\Xi_\omega+\omega^2}`$, without FRAG ([RESTARTS.md](RESTARTS.md) §3); now
  $`m_3 \ge \Lambda_\varepsilon \gt \Phi_1`$ ([REACHES.md](REACHES.md) §5); from replayed certificates, $`m_3`$ is above the point of
  $`\Phi_3((0,0,0)(1,1,1)(2,2,2)(3,3,3))`$; $`m_3`$ is a $`\upsilon`$-point and $`c_0`$ is a
  fixed point of $`\iota \mapsto \upsilon_\iota`$ that lies $`\omega^\omega`$ levels deep in a ladder of such classes (Theorem C3-VEB,
  [PINS.md](PINS.md) §4; its hypothesis INC1 is now proved, [BREAK.md](BREAK.md) §1); $`m_3`$ and every fan apex lie above the first
  non-skeletal point ($`\nu`$ in $`R_2^S`$, Lemma CAP; $`\nu_C`$ in $`R_2^C`$, Theorem NU-CT), which is $`\gt \nu_P`$, and $`m_3 \gt \nu_P`$ has 2 reviews in
  $`R_2^S`$ ([BREAK.md](BREAK.md) §2–3); the least tops of nested pairs of every depth lie below $`m_3`$ (NEST, 2 reviews, [BREAK.md](BREAK.md) §5); every
  fan apex lies above their limit $`T_\omega`$, with no hypothesis (2 reviews); the least fan has exactly two $`\lt_2`$-successors, the second
  equal to its reach, and in $`R_2^C`$ it is open, so it lies strictly below the least closed fan; given the hypothesis $`FF_N`$ (open) the
  first fan, $`m_3`$ and $`C^*_3`$ need an inaccessible ([BREAK.md](BREAK.md) §7.4). In $`R_2^C`$ ([COVER.md](COVER.md), 1 review each): a point of the core is the
  bottom of a chain of length 3 iff it has an infinite $`\le_1`$-chain of right ends (Theorem CP3); $`c_0`$ is the least such point, and $`c_1`$ is
  the supremum of an $`\omega`$-sequence made by downward 2-reflection (LEAST3); the least closed $`n`$-fans (apexes $`\varphi_n`$) stay below $`m_3`$, so
  $`c_0 \gt m_3 \ge \sup_n \varphi_n \gt f_0 \gt x_F`$ (FIN-FAN); given $`FF_{cl}`$ ($`\sup_n \varphi_n \ge \theta_0`$), $`C^*_3`$ needs an inaccessible; whether the first fan
  needs one is the single statement that the point of $`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)), which is $`\min\{m : m \le_1 x_F\}`$, is $`\ge \theta_0`$. Now (1 review each,
  [COVER.md](COVER.md) §5.2–5.3): the least fan has order type $`\omega^2`$; that statement is equivalent to a lower bound for fan-free patterns whose
  right ends have no reach, and it follows from the lower-bound program below $`\theta_0`$; and $`c_2 \lt \omega_1^{CK}`$.
  Earlier:
  $`C^*_2 = \{\upsilon_\omega, \upsilon_{\omega+1}\}`$.
- **Lemma TOP2** (2026-10, 1 review). For every $`\alpha \lt m_3`$ there is a chain $`x \lt_2 y`$ of length 2 with
  $`\alpha \lt x \lt y \lt m_3`$. So $`m_3`$ is a limit of chains of length 2, and $`m_3 \ge \upsilon_{\omega\cdot\omega}`$ without FRAG.
- **Lemma REL** (2026-10, 1 review; Theorem STEP with another start). Let $`r_0 = \tau`$, $`r_{\xi+1} = T^{r_\xi} \cap \Omega_1`$,
  and the supremum at limits. If $`\tau`$ is an $`\varepsilon`$-number, $`\tau \le \psi_{\Omega_1}(A)`$, $`\Omega_\omega \le A`$ and (HA) holds
  for $`A + \theta\cdot\zeta`$ ($`\zeta \lt \Gamma_0`$), then $`r_{1+\eta} \le \psi_{\Omega_1}(A + \theta\cdot(1+\eta))`$ for $`\eta \lt \Gamma_0`$. So a
  restart above $`\psi_{\Omega_1}(A)`$ costs $`+\theta`$ per step, not $`+\Omega_\omega`$.
- Small lemmas: **PRINC** ($`x \lt_1 y`$ gives $`x`$ additive principal; $`x \lt_2 y`$ gives $`y`$ additive
  principal), **ISO-UNION** (a finite union of isominimal sets is isominimal), **HULL** (every regular
  uncountable $`\kappa`$ is $`\le_1`$ to everything above it, in both structures), **DOM₁** (a pattern without
  $`\lt_2`$-pairs has its least realization below $`\upsilon_1`$).
- **Chains made by $`\Phi_3`$** (2026-10, 1 review). **Theorem A**: for every input matrix (standard or not), the
  $`\le_2`$ relation that $`\Phi_3`$ outputs has no $`x \lt_2 y \lt_2 z`$: the right end of a pair is never a left end. So its
  chains have length at most 2. **Theorem B** (one direction): close this relation under transitivity and under
  Carlson's rule "$`a \le_2 b`$ and $`a \le_1 x \le_1 b`$ give $`a \le_2 x`$". Write BAR_R for: if $`a`$ has right ends
  $`d_1 \lt \dots \lt d_q`$ and a node $`y`$ that can be a left end lies between $`d_{k-1}`$ and $`d_k`$ ($`d_0 = a`$), then not
  $`y \le_1 d_k`$. BAR_R implies that the closure has no chain of length 3 (the other direction is not proved).
  **Corollary C**: if $`\Phi_3(M)`$ is a pattern (Carlson 2009, Def 5.6), it has no chain of length 3, so by DOM₂ its point is
  below $`m_3`$ (in $`R_2^C`$). **Lemma LAM**: the spans of two pairs are nested or disjoint; nested ones occur. A
  property CONE of the reach implies BAR_R. Open: BAR_R and CONE. BAR_R fails on some non-standard inputs, so a proof
  must use standardness.
- **Toward an explicit chain of length 3** (2026-10, 1 review). Results on the upper half of Conjecture C3′:
  - **Set-theoretic reflection.** ELEM: if $`H`$ is an elementary submodel of some $`H(\vartheta)`$ and $`H \cap \gamma = \delta`$ is an
    ordinal, then $`R_2|\delta`$ is an elementary substructure of $`R_2|\gamma`$ (in $`R_2^S`$ and $`R_2^C`$). CLUB-1: for regular
    uncountable $`\kappa`$, the $`\delta \lt \kappa`$ with $`\delta \le_1 \infty`$ contain a club. CHAINS-S: in $`R_2^S`$ any two of them are
    $`\le_2`$, so $`R_2^S`$ has chains of every finite length among countable ordinals. HIGH: each such $`\delta`$ is above
    $`\omega_1^{CK} \gt \psi_{\Omega_1}(\Lambda)`$, so this never gives a chain inside the range of InaccPsi.
  - **$`\le_2`$ at a cardinal.** LOCAL-2: the copy from HULL passes the extension clause of T2 for all extensions below
    $`\pi(\beta)`$ (it needs $`Y \subseteq H`$); it can fail only through points in $`[\pi(\beta), \kappa)`$. CHANG-2 (conditional): a
    Chang-type hull hypothesis gives $`\kappa \le_2 \lambda`$ in $`R_2^S`$, and the hypothesis forces $`\lambda \ge \kappa^+`$. SC2:
    $`V_\kappa \prec_{\Sigma_2} V_\beta`$ gives $`\kappa \le_2 \beta`$ in $`R_2^S`$. I0-NOT-SIGMA2: if $`I_0`$ is the least weakly inaccessible,
    $`V_{I_0}`$ is $`\Sigma_2`$-elementary in no $`V_\beta`$ with $`\beta \ge I_0 + 2`$. REFORM: "$`I_0 \le_2 \lambda`$" is equivalent to a
    statement about two ordinals above $`\omega_1^{CK}`$. Open: whether $`I_0 \le_2 \beta`$ for some $`\beta \gt I_0`$.
  - **NO-PROMOTE.** $`\tau = \upsilon_{\omega^2}`$ is an $`\varepsilon`$-number with $`\tau \le_1 \upsilon_{\omega^2+\omega+1}`$ (the restart $`r_{\omega+1}`$
    above $`\tau`$), but $`\{\upsilon_{\omega^2+1}, \upsilon_{\omega^2+\omega}, \upsilon_{\omega^2+\omega+1}\}`$ is not a chain (Lemma TOP and Theorem
    B′′ of R2PLUS; in $`R_2^S`$ without FRAG, in $`R_2^C`$ through EQB′′). So the $`\le_1`$-reach of $`\tau`$ alone cannot prove
    C3′; a proof needs a $`\le_2`$ property of $`c_0`$.
  - **Lemma K and COLLAPSE-FAIL.** The collapse of the hull $`\mathrm{Cl}(0, 0) \cap \Omega_2`$ is the substitution
    $`\Omega_1 \mapsto \Gamma_0`$ (proved). $`\Omega_1 \le_1 \varepsilon_{\Omega_1+1}\cdot 2`$ (proved). "Not $`\Gamma_0 \le_1 \varepsilon_{\Gamma_0+1}\cdot 2`$" is
    **not proved**: the review found a blocking point (the proof uses the right end itself as a point of $`Y`$, which
    the test T1 does not allow). The referee proposed a repair, not yet reviewed. If it holds, collapsing an
    InaccPsi hull does not keep $`\le_1`$, so it cannot bring a $`\le_2`$ relation from a cardinal down to a countable value.

**Toward the lower bound** (2026-10, $`R_2^C`$). Write $`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$.

- **Lemma I-FREE.** A countable normal form has no inaccessible symbol iff its value is below $`\theta_0`$. So
  the inaccessible-free terms are exactly the terms below $`\theta_0 \lt \psi_{\Omega_1}(I_0)`$.
- **Lemma OE.** If a map $`F`$ from the normal forms below $`\gamma`$ to pointed patterns makes "the point of the
  least realization of $`F(t)`$" strictly increasing in $`t`$, then $`[0, \gamma) \subseteq \mathrm{Core}(R_2^C)`$.
  **EPS-RED**: $`F`$ is needed only on the terms whose value is an $`\varepsilon`$-number. **FS-OE**: strict increase
  follows from two local steps, "predecessor below $`t`$" and "$`t[n]`$ below $`t`$".
- **RED-BMS.** With Theorem S of [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md), the lower bound below $`\gamma`$ follows from an
  order embedding $`\mu`$ of the $`\varepsilon`$-number terms below $`\gamma`$ into the standard trio matrices below $`V`$
  (below $`V_3`$, with FRAG, now proved). **S-RED**: on the matrices of the Lean class `TrioStdL`, strict increase of the point
  of $`\Phi_3`$ reduces to the single statement "the point of $`\Phi_3(A[k])`$ is below that of $`\Phi_3(A)`$ for all
  $`A`$ and $`k`$" (from the Lean theorem `trio_fs` and the termination of BMS).
- **Lemma MU-A.** On a fragment $`G_A`$ of terms (sums; $`\psi_{\Omega_1}`$ of sums of $`\Omega_\omega`$, $`\omega^{\Omega_\omega + c}`$ and
  $`\theta\cdot\omega^e`$), the recursive map $`\mu`$ to trio matrices is strictly increasing.
- **Lemma UNIF-V.** For $`A_m = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)^m`$, $`m \ge 3`$, and every $`N`$: the point of
  $`\Phi_3(A_m[N])`$ is below that of $`\Phi_3(A_m)`$, given the output shapes of $`\Phi_3`$ (checked for $`m \le 8`$,
  $`N \le 6`$). This extends Theorem V of R2PLUS ($`m = 2`$). For $`m = 3`$ the shapes are now given for all $`N`$ (2026-10,
  1 review), but by a lemma that is written only as a sketch, so $`m = 3`$ is not counted as proved; CORE-C3 does not
  need it.
- **Lemma MU-B** (2026-10, 1 review). A larger fragment $`G_B \supset G_A`$: any countable limit index $`\Omega_\xi`$ (also
  with $`\psi_{\Omega_1}`$-terms inside $`\xi`$), summands $`\omega^{\Omega_\xi\cdot\kappa + c}`$ with countable $`\kappa \ge 1`$ and $`c`$,
  sums of summands with different indices, $`\theta`$-tails, and countable $`\omega^x`$ for
  $`x \ge \psi_{\Omega_1}(\Omega_\omega)`$. The extended map $`\mu_B`$ equals $`\mu`$ on $`G_A`$ and the Lean map `omegaIndexMatrix` on
  $`\psi_{\Omega_1}(\Omega_\xi)`$, $`\xi \lt \varepsilon_0`$ a limit. $`\mu_B`$ is strictly increasing on $`G_B`$, and every image is below SRO.
  Standard images: proved (Lean `trioStdL_omegaIndexMatrix`) only for $`\psi_{\Omega_1}(\Omega_\xi)`$, $`\xi \lt \varepsilon_0`$ a limit;
  elsewhere checked. The review found one blocking point, against the use of MU-B for the core (not against
  MU-B itself): it adds no ordinal to the known part of the core.
  $`G_B`$ has no element in $`[\varepsilon_0, \psi_{\Omega_1}(\Omega_\omega))`$ (proved), so its order type is small (conjecture: about
  the Ackermann ordinal), and Lemma OE gives only $`[0, \mathrm{otp}(G_B))`$. The next step must cover the
  $`\varepsilon`$-numbers between $`\varepsilon_0`$ and $`\psi_{\Omega_1}(\Omega_\omega)`$.
- **Lemma MU-0** (2026-10, 1 review). The normal forms below $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ are order-isomorphic to
  the standard pair sequences (with the empty one) in lexicographic order, by a map $`\mu_0`$ that sends sums to
  concatenations and additive principal terms to sequences with one root. Proved given one citation:
  $`\upsilon_1`$ equals Buchholz's $`\psi_0(\Omega_\omega)`$ (the Lean axiom `core_eq_psi`; its source is Buchholz 1986, not
  Wilken 2007 as first cited), and Lean theorems (`pairOrd_injective`, `range_pairOrd`, `ordOf_append'`, `lemmaR`).
  $`\mu_0`$ is "the value, then the inverse of the pair rank", not a recursion on terms.
- **Lemma MU-B0** (2026-10, 1 review). MU-B holds on $`G_{B0}`$, which is $`G_B`$ with the base widened to every additive
  principal term below $`\upsilon_1`$, with $`\mu_0`$ on the base: $`\mu_B`$ is strictly increasing and every image is below SRO.
  That the images are standard is checked only. **Gap** (proved): $`G_{B0}`$ contains $`[0, \varepsilon_{\upsilon_1+1})`$ and then
  nothing up to $`\upsilon_2 = \psi_{\Omega_1}(\Omega_\omega + \theta)`$. So family (M4) at level 0 adds no ordinal to the proved
  part of the core there (that it adds none at all is plausible, not proved). The next gap is the base one level up
  (arguments $`\Omega_\omega + \zeta`$, $`\zeta \lt \theta`$; Lemma TR1, open).

**Not proved:**

- **The claim above $`\Lambda_\varepsilon`$** in $`R_2^C`$, and above $`\upsilon_{\omega^3}`$ in $`R_2^S`$, both halves. The reaches of the restarts
  above $`\Theta_A`$ (the reach at $`\Theta_A`$ itself is now known), and the rest of [BREAK.md](BREAK.md) §10, [PINS.md](PINS.md) §6, [REACHES.md](REACHES.md) §7 and [RESTARTS.md](RESTARTS.md) §6.
- **$`R_2^S = R_2^C`$**: the converse $`C \Rightarrow S`$ for $`\le_1`$ at a successor stage $`\beta \gt \kappa_C`$ with
  $`\alpha \notin G_C`$, and for $`\le_2`$ at stages of type (ii) (this needs an upward transfer of $`\Pi_2`$ sentences, which
  neither upward 2-reflection nor liftings give; it is now one pair $`(a^*, \beta)`$ per stage, and below $`\kappa_C`$ it is
  Conjecture CORE-2; left: PIN and LOW); Σ2-GAP, INC, W(C), (R), AGR, and $`\beta_0 = \infty`$. Theorem CC and all
  certificates are about $`R_2^C`$.
- **The lower bound below $`\theta_0`$** (referee: blocking gap toward this goal, not an error): an order embedding
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
  (NO-PROMOTE). Carlson 2009, Thm 15.2 gives $`c_2 \lt \omega_1^{CK}`$, but no bound by an InaccPsi term is proved ([COVER.md](COVER.md) §5.2). Lower half open: it needs the lower bound program below $`\theta_0`$ with patterns without a chain of
  length 3.
- That $`\Phi_3(M)`$ is a pattern. Then it has no chain of length 3 (Corollary C), and DOM₂ bounds its point by $`m_3`$.
  The output relation itself has no such chain (Theorem A, proved); for its closure this is BAR_R (checked only).

## 4. Names of Wilken's points (Theorem T)

**Theorem T** (proved; upper half T-UP 2 reviews, lower half T-LOW 1 review). With
$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$, for every $`\eta \lt \Gamma_0`$, in particular for $`\eta \le \omega^2`$, and by Theorem T+
(2 reviews, [RESTARTS.md](RESTARTS.md) §4) for every $`\eta`$ below the first fixed point $`\Xi_1`$ of $`\iota \mapsto \upsilon_\iota`$
(beyond, Theorem T++ of [REACHES.md](REACHES.md) §2 names every $`\Xi_\alpha`$ and the points between them up to $`\Phi_1`$, and
Theorem GEN of [PINS.md](PINS.md) §3 names the $`\upsilon`$-points below $`\upsilon^* \le \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$:
$`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) = \upsilon_{1+\iota(\eta)}`$ for every $`\eta`$ in the set $`D`$ of the $`\eta \lt \Omega_2`$ that give a normal form, with
$`\iota(\eta)`$ the order type of $`D \cap \eta`$; GEN-EXT extends this to $`\eta \lt \Omega_\omega\cdot\omega`$, [BREAK.md](BREAK.md) §2):

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
    - Theorem T, the exact names for $`\eta \lt \Gamma_0`$ — proved (T-UP, T-LOW)
    - $`\mathrm{Core}(R_2^S)`$ contains all of $`\upsilon_{\omega\cdot\omega}`$ — proved (CORE-S)
    - in $`R_2^C`$ up to $`\upsilon_{\omega^3}`$, without FRAG — proved (CORE-C3, PT)
    - in $`R_2^C`$ up to $`\Phi_1`$, and the core of $`R_2^C`$ up to $`\rho_{\Theta_P}`$ — proved (T++, PHI, CORE-C$`^O`$, CORE-C$`^+`$;
      [REACHES.md](REACHES.md))
    - in $`R_2^C`$ up to $`\Lambda_\varepsilon`$, and the core of $`R_2^C`$ up to $`\rho_{\Theta_A+\omega^2}`$ — proved (GEN, NAME-V,
      NAME-OFFSET, CORE-C$`^A`$; [PINS.md](PINS.md))
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
    - B1 explicit chains of every length $`n`$ below $`\psi_{\Omega_1}(I_\omega)`$ as InaccPsi values — open
      (conjecture for $`n = 3`$ in §3)
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
      compared with InaccPsi — open, high (the map $`B`$ of STEP does this below $`\Omega_\omega`$, one way)
    - A2 a structure theorem for $`\le_1`$, $`\le_2`$ of $`R_2^+`$ up to the bound (the analogue of Wilken 2021,
      Thm 4.2); the results of [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md) are this theorem below
      $`\upsilon_{\omega^3}`$, Theorem BLK$`^O`$ extends it with exact reaches to $`\Lambda_\varepsilon`$, Theorem EXACT-A to $`\Theta_A`$
      ([PINS.md](PINS.md)), the value at $`\Theta_A`$ and the landmarks $`\Theta_\delta`$, $`\Theta_{d\omega}`$ ([BREAK.md](BREAK.md) §4), Theorem SKEL gives it in
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
    - A6 $`R_2^S = R_2^C`$ everywhere — open (known below $`\beta_0 \gt \upsilon_{\omega\cdot\omega}`$)
    - A7 relativized patterns of $`R_1^+`$ and uniform assignments between ordinals and patterns (announced by Wilken) —
      proved (RC-PIN, RC, U, UNIF; [PINS.md](PINS.md) §1; the closures are finite, CL-FIN, and are explicit pin patterns, EXPL,
      [BREAK.md](BREAK.md) §4); that the assignments are elementary recursive — outline only
  - **L** lower bound $`\psi_{\Omega_1}(I_\omega) \subseteq \mathrm{Core}(R_2^+)`$ — open
    - L0 in $`R_2^C`$: equivalent to "every $`\gamma \lt \psi_{\Omega_1}(I_\omega)`$ is below some $`\max C^*_n`$" — proved
    - L-CERT below $`\theta_0`$: reductions proved (I-FREE, OE, EPS-RED, FS-OE, RED-BMS, S-RED, MU-A, MU-B, UNIF-V);
      also MU-0 and MU-B0 ((M4) at level 0; adds nothing to the core); left: (M4) at level $`\ge 1`$, (M1)–(M3), and the
      local step below SRO — open (with them the first fan needs an inaccessible, RED-HM, [COVER.md](COVER.md) §5.3)
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
      the least fan is described, with order type $`\omega^2`$ (FS, OF; [COVER.md](COVER.md) §2, §5.2); $`c_2 \lt \omega_1^{CK}`$)
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
  refuted; 30 reversed pairs: 0. For $`V_3`$ itself: 11 of 11 certificates for $`N \le 10`$, replayed.
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
results by covering minimality and the level-0 description (the fifth and sixth rounds) on the sixth page [COVER.md](COVER.md).

## 8. References

- T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001).
- T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009).
- T. J. Carlson, G. Wilken, "Normal forms for elementary patterns", JSL 77 (2012).
- G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
- G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
- A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined θ-functions", MLQ 57 (2011).
- G. Wilken, "A glimpse of Σ₃-elementarity" (2020).
- G. Wilken, "Pure Σ₂-elementarity beyond the core", APAL 172 (2021).
- W. Buchholz, "A new system of proof-theoretic ordinal functions", APAL 32 (1986).
- W. Buchholz, "A simplified version of local predicativity" (1992).
- W. Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof Theory (1998), Ch. IV.
