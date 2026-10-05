[← Back](README.md) | [English](REACHES.md) | [Japanese](REACHES-ja.md)

# $`R_2^+`$ above $`\Xi_\omega`$: exact reaches, the skeletal regime, and the least chain of length 3

This page continues [RESTARTS.md](RESTARTS.md). The status words are those of [README.md](README.md) §3:
**proved** means that an independent referee found the result proved with no fatal or blocking point. All results
on this page are from 2026-10. "1 review" means one referee. "2 reviews" means that two independent papers proved
the result and each paper was refereed once. The results of the next round (relativized pins, the exact reaches up
to $`\Theta_A`$, the names up to $`\Lambda_\varepsilon`$, the bottom of a chain of length 3) are on the fourth page
[PINS.md](PINS.md), the four rounds after that are on the fifth page [BREAK.md](BREAK.md), the fifth to seventh rounds on the sixth page [COVER.md](COVER.md), and the eighth to tenth on the seventh page [FANFREE.md](FANFREE.md), and the eleventh and twelfth on the eighth page [VEBLEN.md](VEBLEN.md); they change some statuses here, as marked.

**Notation.** As on [RESTARTS.md](RESTARTS.md): $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$, the reach
$`\mathrm{lh}(\alpha) = \max\{\gamma : \alpha \le_1 \gamma\}`$, the restart $`\rho_\lambda = \upsilon_\lambda`$ for a nonzero multiple
$`\lambda`$ of $`\omega^2`$, its first block top $`\delta_\lambda = \upsilon_{\lambda+\omega+1}`$, and $`\Xi_\alpha`$ the $`\alpha`$-th nonzero fixed
point of $`\iota \mapsto \upsilon_\iota`$. "In $`R`$" means in $`R_2^S`$ and in $`R_2^C`$. $`\mathrm{logend}(\alpha)`$ is the exponent of the
last term of the Cantor normal form of $`\alpha`$. $`C^*_3 = \{c_0 \lt c_1 \lt c_2\}`$ is the least chain of length 3 of
$`R_2^C`$ and $`m_3 = \min\{m : m \le_1 c_0\}`$.

## 1. The exact reaches of the restarts

**The Veblen hierarchy over $`\upsilon`$.** $`V_1(\alpha) = \Xi_\alpha`$ ($`\alpha \ge 1`$); $`V_{\gamma+1}`$ enumerates the fixed points of
$`V_\gamma`$; at a limit $`\gamma`$, $`V_\gamma`$ enumerates the common fixed points. The level $`\gamma(\lambda)`$ of a restart index
$`\lambda`$ is the largest $`\gamma`$ with $`\lambda`$ in the range of $`V_\gamma`$ ($`0`$ if $`\lambda`$ is not a fixed point of
$`\iota \mapsto \upsilon_\iota`$). $`\Lambda_\Gamma`$ is the least $`\lambda`$ that is in the range of $`V_\gamma`$ for every $`\gamma \lt \lambda`$.

**The recursive offset $`O(\lambda)`$** (defined from the $`O(\mu)`$, $`\mu \lt \lambda`$). An offset term $`t`$ is a Cantor normal
form built from one variable $`x`$ and constants by sums and $`t \mapsto \omega^t`$, or the term $`\varepsilon_{x+1}`$. A restart
$`\rho_\mu`$ realizes $`t`$ if $`O(\mu) \ge t(\rho_\mu)`$. Then $`O(\lambda)`$ is the supremum of $`t(\rho_\lambda) + 1`$ over the terms $`t`$
that cofinally many restarts below $`\lambda`$ realize. $`\Lambda_\varepsilon`$ is the least $`\lambda`$ below which $`\varepsilon_{x+1}`$ is
realized cofinally.

- **Theorem BLK$`^O`$** (proved, 1 review). For every restart index $`\lambda \lt \Lambda_\varepsilon`$, the statements (i)–(iii) of
  Theorem BLK$`^\Xi`$ ([RESTARTS.md](RESTARTS.md) §3) hold in $`R`$ below $`\upsilon_{\lambda+\omega^2}`$, with the exact reach
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + O(\lambda)`$. The upper end (Lemma TOP$`^O`$) uses no FRAG; the lower end (Lemma
  RS$`^O`$) uses FRAG. Two new lemmas carry the proof. **EXACT**: a base change $`\pi`$ of Wilken moves an offset term
  exactly, $`\pi(t(r)) = t(s)`$ (Wilken, APAL 145 (2007) 130–161, Lemma 4.2 and Def 5.1). **IMG**: a covering copy of
  an offset term is not below the same term at the new base (Wilken, APAL 145 (2007) 162–175, Thm 2.2). The target
  of the copy is a restart chosen by the cofinality in the definition of $`O`$, so the error of the old sketch
  RS$`_\lambda`$ does not arise.
- **Corollary EQB$`^O`$** (proved, 1 review). $`R_2^S`$ and $`R_2^C`$ agree on every pair below $`\Lambda_\varepsilon`$, so the first
  difference $`\beta_0`$ is at least $`\Lambda_\varepsilon`$.
- **Theorem OFF-V** (proved, 1 review). For every restart index $`\lambda \lt \Lambda_\Gamma`$: if $`\gamma(\lambda) = 0`$ and
  $`\lambda = \lambda_0 + \omega^e`$, then $`O(\lambda) = -1 + e`$; if $`\lambda = V_\gamma(\alpha)`$ with $`\gamma = \gamma(\lambda) \ge 1`$, then
  $`O(\lambda) = \rho_\lambda\cdot\gamma + \mathrm{logend}(\alpha)`$. Also $`O(\Lambda_\Gamma) = \omega^{\rho\cdot 2}`$, so $`\Lambda_\Gamma \lt \Lambda_\varepsilon`$. Now ([FANFREE.md](FANFREE.md) §3, Theorem GEN-OFF) the same formula holds
  for the formal-reach recursion at every restart index below $`\nu`$ that is not in the range of $`V_\gamma`$ for every $`\gamma \lt \lambda`$ (proved
  for $`\gamma(\lambda) = 0`$, outline for $`\gamma(\lambda) \ge 1`$). Now (1 review, Theorem LAYERS, [FANFREE.md](FANFREE.md) §7.3) it is proved in full, and extended through
  all layers above $`\upsilon`$: every restart below $`\nu`$ has a known reach except at limits of critical indices. Then (1 review, Theorem KV,
  [FANFREE.md](FANFREE.md) §10.3) the formula extends to offsets below $`\rho^\rho`$ by a Klammer hierarchy over $`\upsilon`$. Then (1 review,
  Theorem KV-NAMES, [VEBLEN.md](VEBLEN.md) §1) the Klammer form of each such restart is read off its InaccPsi name, and the formula holds in
  closed form for every restart with $`e_\lambda \le \psi_{\Omega_2}(\Omega_2) + 1`$ (NAME-OFFSET-G), and then (1 review, [VEBLEN.md](VEBLEN.md) §8) with
  $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$ (NAME-OFFSET-G⁺).
- **Lemma RS$`_\lambda`$** (proved, 2 reviews). For every restart index $`\lambda \le \Xi_\omega`$, in $`R`$:
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^*(\lambda)`$. This is BLK$`^O`$ with OFF-V. The second proof is Theorem EXACT of §3.
- **Theorem EXACT and OFF-k** (proved, 1 review; a second, independent proof of the exact reaches). With a formal
  offset $`c^+`$ defined by base changes, $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^+(\lambda)`$ in $`R`$ for every
  $`\lambda \lt \Theta_P`$, where $`\Theta_P`$ is the least $`\lambda`$ with $`c^+(\lambda) \ge \varepsilon_{\rho_\lambda+\omega}`$. The upper bound uses no
  FRAG (new Lemma PIN, from Wilken's Thm 2.2 above); the lower bound uses FRAG. The closed form of $`c^+`$ up to
  $`\Theta_{add} = V_\omega(1)`$, the least common fixed point of all $`V_k`$ ($`k \lt \omega`$), is the one of OFF-V, and
  $`c^+(\Theta_{add}) = \rho\cdot\omega`$. So the exact reach and its closed form have **2 reviews** for every restart
  index $`\lambda \le V_\omega(1)`$. Proved order: $`\Xi_\omega \lt V_\omega(1) \lt \Theta_P`$. Extended past $`\Theta_P`$ to $`\Theta_1`$ (2 reviews) and
  $`\Theta_A`$ (1 review) in [PINS.md](PINS.md) §2.

| $`\lambda`$ | $`O(\lambda)`$ | $`\lambda`$ | $`O(\lambda)`$ |
|---|---|---|---|
| $`\omega^3,\ \omega^4,\ \omega^\omega`$ | $`2,\ 3,\ \omega`$ | $`\Phi_1 = V_2(1)`$ | $`\rho\cdot 2`$ |
| $`\omega^{\Xi_\omega+1}`$ | $`\Xi_\omega + 1`$ | $`V_2(\omega)`$ | $`\rho\cdot 2 + 1`$ |
| $`\Xi_n`$ ($`1 \le n \lt \omega`$) | $`\rho`$ | $`V_3(1)`$ | $`\rho\cdot 3`$ |
| $`\Xi_\omega`$ | $`\rho + 1`$ | $`V_\omega(1)`$ | $`\rho\cdot\omega`$ |
| $`\Xi_{\omega^\omega}`$ | $`\rho + \omega`$ | $`\Lambda_\Gamma`$ | $`\omega^{\rho\cdot 2}`$ |

The old failure of the offset lemma at $`\lambda = \omega^{\Xi_\omega+1}`$ is resolved: there $`O = \Xi_\omega + 1 = -1 + e`$. Conjecture
CAP of [RESTARTS.md](RESTARTS.md) §2 agrees with OFF-V at every restart of level 0 and fails at $`\Xi_\omega`$ (it gives
$`\rho`$; the reach has $`\rho + 1`$).

## 2. The core of $`R_2^C`$ and the names up to $`\Phi_1`$

- **Theorem CORE-C$`^O`$** (proved, 1 review; no FRAG). $`[0, \Lambda_\varepsilon) \subseteq \mathrm{Core}(R_2^C)`$. Corollary (proved,
  1 review): $`\Lambda_\varepsilon \lt \Omega_1`$ (after a citation repair by the referee: Carlson 2009, Lemma 15.11, Thm 14.14 and
  Cor 15.15), $`\min C^*_3 \ge \Lambda_\varepsilon`$, $`m_3 \ge \Lambda_\varepsilon`$, and $`\kappa_S \ge \Lambda_\varepsilon`$.
- **Theorem CORE-C$`^+`$** (proved, 1 review; no FRAG). $`[0, \rho_{\Theta_P}) \subseteq \mathrm{Core}(R_2^C)`$, and on this segment $`R_2^C`$
  has the pairs and blocks of $`R_2^S`$ and equals it (using FRAG). So $`\beta_0 \ge \rho_{\Theta_P}`$. Now extended to
  $`[0, \rho_{\Theta_A+\omega^2})`$ ([PINS.md](PINS.md) §2).
- **Theorem T++** (proved, 3 reviews; the third proof is Theorem GEN of [PINS.md](PINS.md) §3). Let $`\Phi_1`$ be the least $`\alpha \ge 1`$ with $`\Xi_\alpha = \alpha`$; it is $`V_2(1)`$. For
  $`1 \le \alpha \lt \Phi_1`$:
  $`\Xi_\alpha = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot\alpha)`$, and
  $`\upsilon_{\Xi_\alpha + x} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot\alpha + \theta\cdot x)`$ for $`x \lt \Xi_{\alpha+1}`$.
  In particular $`\Xi_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1})`$ (the old conjecture),
  $`\Xi_\omega = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1+1})`$, and Lemma REL above $`\Xi_1`$ is an equality. Tools: Lemma SUB
  and the hull lemma HL (first paper); Lemma GAP, the countable part of the hull $`\mathrm{Cl}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot(z+1), s)`$
  stays below $`s`$ (second paper).
- **Theorem PHI** (proved, 2 reviews; the second proof is in [PINS.md](PINS.md) §3). $`\Phi_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$.
- So **Wilken's claim holds on $`[0, \Phi_1]`$ in $`R_2^C`$**, both halves: every ordinal there is in the core and is the
  value of an InaccPsi normal form with collapse arguments at most $`\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2} \lt I_\omega`$
  (2 reviews). Before: $`[0, \Xi_1]`$. Now it holds on $`[0, \Lambda_\varepsilon)`$ ([PINS.md](PINS.md) §3).
- **Below $`\Xi_1`$ in InaccPsi terms** (proved, 1 review; Conjecture 42+.I of [RESTARTS.md](RESTARTS.md) §5 is now a
  theorem there). With $`A = \omega^{\theta+a_1} + \cdots + \omega^{\theta+a_k}`$ ($`a_1 \ge \cdots \ge a_k = e \ge 2`$): the pairs are
  $`\psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1}\cdot j) \lt_2 \psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1}\cdot j + \theta)`$, the
  restart is $`\psi_{\Omega_1}(\Omega_\omega + A)`$, and its reach is $`\psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1} + \theta) + (-1 + e)`$.
- **Conjectures, now proved** ([PINS.md](PINS.md) §3; NAME-OFFSET in a corrected form). NAME-V: $`V_\gamma(\alpha) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot\gamma}\cdot\alpha)`$ ($`\gamma \ge 1`$). NAME-OFFSET: if
  the last summand of the name of $`\rho_\lambda`$ is $`\omega^{\theta+e}`$, then $`O(\lambda)`$ is $`-1 + e`$ with $`\Omega_1`$ replaced by
  $`\rho_\lambda`$. They give $`\Lambda_\Gamma = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1^2})`$ and
  $`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$.

## 3. The skeletal regime (Theorem SKEL)

Let $`\Lambda^*`$ be the least restart index $`\lambda`$ whose reach leaves its own region, $`\mathrm{lh}(\rho_\lambda) \ge \rho_{\lambda+\omega^2}`$,
and $`\nu_P = \upsilon_{\Lambda^*+\omega^2}`$.

- **Theorem SKEL** (proved, 1 review; $`R_2^S`$; no FRAG). $`\Lambda^*`$ exists and is countable, and below $`\nu_P`$:
  (i) the $`\lt_2`$-pairs are exactly $`(\upsilon_\xi, \upsilon_{\xi+1})`$ with $`\mathrm{logend}(\xi) = 1`$; (ii) a restart has no
  $`\lt_1`$-predecessor and no $`\lt_2`$-successor, and its reach lies in its own region and is closed (every point between
  the restart and its reach has its reach at most there); (iii) every other point lies in a block with top $`d`$, and its
  reach is the smaller of its $`R_1^+`$ reach and $`d`$; (iv) $`R_2^S`$ is skeletal on $`[0, \nu_P]`$. At $`\nu_P`$ the description
  first fails: $`\rho_{\Lambda^*} \lt_1 \nu_P`$. The new tool, Lemma C′, allows the reach in any block, so the value of the
  reach is not needed. Proved too: $`\Theta_P \le \Lambda^*`$, and every chain $`c_0 \lt_2 c_1 \lt_2 c_2`$ of $`R_2^S`$ has $`c_0 \ge \nu_P`$.
- **Not proved.** $`R_2^C`$ on $`[\rho_{\Theta_P}, \nu_P)`$: only an outline, under the open hypothesis HC (the $`R_2^C`$ reach of
  every restart below $`\Lambda^*`$ is at most its $`R_2^S`$ reach). The exact reaches on $`[\Theta_P, \Lambda^*]`$: the lower bound
  of a general transport form is proved (using FRAG); the upper bound needs a relativized core of $`R_1^+`$ that Wilken
  announces (APAL 145 (2007) 162–175, p. 174) in a paper we do not have. Now: that core is rebuilt, the exact reaches are
  known up to $`\Theta_A`$, HC holds below $`\Theta_A`$, and $`R_2^C`$ is known on $`[0, \rho_{\Theta_A+\omega^2})`$ ([PINS.md](PINS.md) §1–2).
- **Conjectures** (checked with the program). $`\upsilon_{\Lambda^*} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2})`$ with
  $`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$, the point of the matrix (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,2,0)(3,3,1)(3,0,0)(3,0,0);
  $`\nu_P = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$. (Now both are proved as lower bounds, as a transfer of refereed proofs, 1 review, and the name of
  $`\upsilon_{\Lambda^*}`$ comes out of that derivation independently; equality is still a conjecture, [THETA.md](THETA.md) §1. Now both names are proved, [THETA.md](THETA.md) §9.1.)

## 4. Where the skeleton ends

$`R_2^+`$ is skeletal on a set if (SK1) every point that is not a $`\upsilon`$-point has its $`R_1^+`$ reach there, and (SK3) every
$`\lt_2`$-pair is $`(\upsilon_\xi, \upsilon_{\xi+1})`$ ([RESTARTS.md](RESTARTS.md) §2). $`\nu_S`$ and $`\nu_C`$ are the first points where
$`R_2^S`$ and $`R_2^C`$ stop being skeletal. INC1-nonups is the statement "if $`a`$ is not a $`\upsilon`$-point and $`a \le_1 b`$ in $`R_2^C`$,
then $`a \le_1 b`$ in $`R_1^+`$"; it was first proved below $`\upsilon_{\Xi_\omega+\omega^2}`$. INC1-S is the same for $`R_2^S`$ and every $`a`$.
Both are now proved everywhere (Theorem INC1, 1 review, [BREAK.md](BREAK.md) §1).

**Status change** (blocking point found in the next round, [PINS.md](PINS.md) §4). The proof of LEFT in $`R_2^S`$ assumed that
$`\Sigma_1`$-elementarity in the language of $`R_2^S`$ gives $`\le_1`$ of $`R_1^+`$; it does not. So LEFT, and every result below that uses
it (3CH, FIRST-BREAK, FRAG2-W, FRAG2-C, and C3′-FALSE of §5), holds in $`R_2^S`$ only given INC1-S.
**Second status change** ([BREAK.md](BREAK.md) §1, 1 review). LEFT holds for every left end below the first bad right end, which in
$`R_2^S`$ lies above $`\nu_P`$, and everywhere given Conjecture NOBAD (in $`R_2^C`$ also given CC). FIRST-BREAK and 3CH (iv) are
unconditional again; the other results hold given NOBAD, and unconditionally low enough.
**Third status change** ([BREAK.md](BREAK.md) §1, 1 review). NOBAD, INC1-S and INC1-nonups are proved. So LEFT, and every result
below that used it, now holds with no hypothesis.

- **Lemma LEFT** (first proved given INC1-S in $`R_2^S`$ and given INC1-nonups in $`R_2^C`$, 1 review; now proved, see above). Every $`\lt_2`$-left end is $`\upsilon_\lambda`$ with $`\lambda`$ a
  limit. **Corollary 3CH**: in every chain $`c_0 \lt_2 c_1 \lt_2 c_2`$, $`c_0 = \upsilon_\Lambda`$ with $`\Lambda`$ a restart index and
  $`c_1 = \upsilon_\mu`$ with $`\mu`$ a limit; so $`\nu_S \le c_1`$.
- **Theorem FIRST-BREAK** (proved, 1 review, and unconditional by [BREAK.md](BREAK.md) §1, 1 review; $`R_2^S`$). $`\nu_S = \min(\nu_a, \nu_b)`$, where $`\nu_a`$ is the least $`b`$ with
  $`\upsilon_\lambda \lt_2 b`$ and $`b \ne \upsilon_{\lambda+1}`$, and $`\nu_b`$ is the least $`\mathrm{cap}(u) + 1`$ such that the cap of a $`\upsilon`$-point $`u`$
  cuts the $`R_1^+`$ reach of a point $`a`$ that is not a $`\upsilon`$-point ($`u \lt a \le \mathrm{cap}(u) \lt \mathrm{lh}_1(a)`$). Also proved:
  $`\nu_S \gt \nu_P`$ (§3).
- **The skeleton breaks below $`m_3`$** (proved, 2 reviews). Theorem NU-C: $`\upsilon_{\Xi_\omega+\omega^2} \le \nu_C \lt m_3`$, because the
  pattern "a point with two $`\lt_2`$-successors" has no chain of length 3, so DOM₂ puts its least realization below $`m_3`$.
  Lemma FAN (both structures, no FRAG): for a chain $`d_0 \lt_2 d_1 \lt_2 d_2`$ and $`m \lt d_0`$ with $`m \le_1 d_0`$, points with two
  $`\lt_2`$-successors are cofinal below $`m`$. So chains of length 3 do not start at the first non-skeletal point.
- **From replayed certificates** ($`R_2^C`$; proved, 1 review). Every point with two $`\lt_2`$-successors lies above the point of
  $`\Phi_3(\mathrm{SRO})`$. $`\nu_C`$ is below the point of $`\Phi_3`$ of row 28 of the table in [README.md](README.md) §6: first given INC1-nonups,
  now without any hypothesis ([BREAK.md](BREAK.md) §2).
- **Base changes beyond the skeleton** (proved with their stated hypotheses, 1 review, using FRAG). FRAG2-W: Theorem
  FRAG2 needs only SK1. FRAG2-C: with the extra datum $`\mathrm{Cut}(a) = \min\{\mathrm{cap}(u) : u \text{ a } \upsilon\text{-point}, u \le_1 a\}`$ it holds
  where reaches are "cut-skeletal". FRAG2-1E: one base change between any two $`\varepsilon`$-bases (the $`R_2^+`$ form of Wilken's
  $`\iota_{\tau,\alpha}`$), under Wilken's side condition. By LEFT only $`\upsilon`$-points are $`\lt_2`$-left ends, so other bases carry
  only $`\le_1`$ data. FRAG2-W and FRAG2-C also assumed INC1, which is now proved ([BREAK.md](BREAK.md) §1). **Not proved** (blocking point): the ranges "FRAG2-W up to $`\nu_b`$" and "cut-skeletal beyond $`\nu_b`$"; the
  proof assumes SK3, which fails above $`\nu_a`$. The referee's fix: restrict them to $`[0, \nu_S)`$ ($`\nu_S`$ is now known exactly,
  [BREAK.md](BREAK.md) §2).
- **Conjecture NS.** $`\nu_S = \nu_C`$ is the top of the least "pair with a nested pair", between $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ and
  $`\psi_{\Omega_1}(\omega^{\Omega_\omega+1})`$, far below $`\theta_0`$; the first inaccessible enters only with the first point with two
  $`\lt_2`$-successors. Now: for $`R_2^S`$, "$`\nu_S`$ is the top of the least pair with a nested pair" is proved (Theorem FIRST-PAIR,
  1 review, [BREAK.md](BREAK.md) §2); its name ($`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'+1} + \theta')`$ with $`\theta' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$, inside the
  conjectured interval) stays a conjecture. In $`R_2^C`$, $`\nu_C = T_C \le \nu_S`$, and $`\nu_C = \nu_S`$ unless $`R_2^C`$ has one extra "ghost" pair
  (Theorem NU-CT, 1 review, [BREAK.md](BREAK.md) §2); $`\nu_C = \nu_S`$ is open. Now (1 review each, [BREAK.md](BREAK.md) §7.3): the name of $`\nu_S`$ is
  equivalent to three statements about $`\upsilon`$-indices, and $`\nu_C = \nu_S`$ is a question about $`R_2^S`$ alone, reduced to two statements
  about it. Then (1 review each, [BREAK.md](BREAK.md) §8): one of them, $`o_2 = \omega`$, is proved in $`R_2^C`$, so $`\nu_C = \upsilon^2_{\omega+1}`$ there;
  $`\nu_C = \nu_S`$ implies $`o_2 = \omega`$ in $`R_2^S`$; the other, NOLIM above $`\nu_P`$, is reduced to one statement per gap. Then (1 review each,
  [COVER.md](COVER.md) §3): NOLIM holds in $`R_2^C`$ (at proof level since [COVER.md](COVER.md) §5.1), and $`\nu_C = \nu_S`$ is equivalent to NOLIM and $`o_2 = \omega`$ in $`R_2^S`$. Then (1 review each,
  [COVER.md](COVER.md) §6.3): it is equivalent to one $`\Sigma_2`$ statement inside the common structure below $`\nu_C`$, and it follows from a
  condition on the segments of level 2 that is proved on the first block. $`\nu_C = \nu_S`$ is still open.

## 5. The least chain of length 3

- **Lower bound** (proved). $`m_3 \ge \Lambda_\varepsilon \gt \Phi_1`$ (§2, 1 review), so $`m_3 \gt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$.
  A second paper proves the weaker $`m_3 \gt \upsilon_{\Xi_\omega+\omega^2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1+1} + \omega^{\theta+2})`$ (1 review).
  The shape of the bottom of a chain (now unconditional) and stronger bounds are in [PINS.md](PINS.md) §4, and the bounds
  $`c_0 \gt m_3 \ge \sup_n \varphi_n \gt f_0 \gt x_F \gt T_\omega`$ of the fifth round ($`\varphi_n`$ the least apex of a closed $`n`$-fan) in [COVER.md](COVER.md) §1.
- **C3′ in its heuristic form is false** (first proved given INC1-S in $`R_2^S`$ and INC1-nonups in $`R_2^C`$, 1 review; now unconditional,
  [BREAK.md](BREAK.md) §1). The next restart $`r_1(\tau)`$ above $`\tau`$ is the least $`\upsilon`$-point
  above $`\tau`$; its index is a successor, so by LEFT it is never a $`\lt_2`$-left end, and the restarted triple
  $`\{r_1, r_\omega, r_{\omega+1}\}(\tau)`$ is never a chain. The numeric form of C3′ ([README.md](README.md) §3) has lost its derivation; it
  stays a conjecture. Corrected shape C3′′ (conjecture): $`C^*_3 = \{\upsilon_\Lambda, \upsilon_{\Lambda+\omega}, \upsilon_{\Lambda+\omega+1}\}`$ for a restart
  index $`\Lambda`$. The referee points out evidence against it: in pure $`R_2`$ the least chain has indices
  $`(\Lambda, \Lambda\cdot\omega, \Lambda\cdot(\omega+1))`$ (Wilken 2021). Now C3′′ is false (Theorem C3′′-FALSE, 1 review, unconditional,
  [BREAK.md](BREAK.md) §3).
- **NO-GEN** (proved, 1 review; $`R_2^C`$). A covered pattern without a chain of length 3 generates (Carlson 2009, Defs 9.1,
  9.4, 10.1, 13.10, Thm 14.11) only patterns without one. So the chain must be in the seed, and Carlson proves the seed
  covered only by Lemma 15.11 (set theory, with witnesses above $`\omega_1^{CK}`$).
- **GEN-OTP** (proved, 1 review; from Carlson 2009, 14.7–14.10, 15.1). Generating fairly from the abstract pattern of a
  chain of length 3 gives a structure isomorphic to an initial segment of the ordinals, and each $`c_i`$ is the order
  type below the $`i`$-th seed point. So the upper half of C3′ is an ordinal analysis of this structure.
- **Given Conjecture MONO** ($`\le_1`$ of $`R_2`$ is contained in $`\le_1`$ of $`R_1^+`$; proved, 1 review): $`m_3`$ is a $`\upsilon`$-point, or
  $`c_2`$ is below the least $`\upsilon`$-point above $`m_3`$.
- **Not proved as stated** (blocking point): a form of TOP$`_\lambda`$ for offsets $`\rho\cdot k + c`$; it needs the extra hypothesis
  $`\tau \lt_2 \delta`$ above the restart, and with it, it is proved. No proved bound uses it; below $`\Lambda_\varepsilon`$ TOP$`^O`$ covers it.
- **Conjectures.** OFFSET-W and BLK-GEN (the skeleton continues while offsets have the form $`\rho\cdot k + c`$); under them
  the skeleton method reaches at most about $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$, far below
  $`\psi_{\Omega_1}(\varepsilon_{I_0+1})`$.

## 6. Checks

Each run was under 60 seconds; none is a proof.

- The program `phi3def2` on 13 standard matrices above $`\Xi_\omega`$: every reach is $`\delta + O(\lambda)`$ when its nodes are read
  with Wilken's Thm 2.2 (the referee notes that these node values are the predictions that match, not values the
  program computes). The referee: 10 new matrices, all as predicted.
- Certificates: 25 of 25 found and replayed (9 consecutive points from $`\Xi_\omega`$ up, 16 pairs $`M[N] \lt M`$), 0 of 9 in
  the reversed direction; the referee replayed 25 of 25 again. For §4: 5 certificates replayed by the referee.
- Names: 21 and 18 InaccPsi terms, all normal forms and strictly increasing, in Python and in Lean. The referee's
  random test of normal forms below $`\Xi_1`$ and $`\Xi_2`$ (about 1.9 million hits): 0 counterexamples to Lemma GAP.
- 598 standard matrices from (0,0,0)(1,1,1)(1,1,0)(2,2,1) on: every pair of the program has the reach of its left end
  at its right end, no two pairs nest, and a restart's reach passes the next restart exactly from the matrix of
  $`\Lambda^*`$ on (40 patterns). The first program pattern that breaks the skeleton is $`\Phi_3`$ of row 27 of the table
  in [README.md](README.md) §6 ($`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$); there are none on more than 14,000 patterns between $`\Xi_\omega`$
  and it (the scan ranges overlap).

## 7. Open

- The exact reaches above $`\Theta_A`$ (above any base below $`T_\omega`$ they follow the formal-reach recursion run above that base;
  now proved, 1 review, [COVER.md](COVER.md) §5.1); the reaches up to $`\Theta_A`$, and the closed form of $`O`$ on $`[\Lambda_\Gamma, \Lambda_\varepsilon)`$, are
  now proved ([PINS.md](PINS.md) §2–3).
- $`R_2^C`$ above $`\nu_C`$ (the core of $`R_2^C`$ now contains $`[0, \nu_C]`$ with $`\nu_C \gt \nu_P`$, [BREAK.md](BREAK.md) §2; now $`\nu_C \gt \upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$, and $`\nu_P \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ as a transfer, [THETA.md](THETA.md) §1; now $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$, [THETA.md](THETA.md) §9.1; then $`\nu_C \ge X_4`$, [SHIFT.md](SHIFT.md) §1). INC1-nonups and INC1-S are now
  proved ([BREAK.md](BREAK.md) §1).
- The values of $`\Theta_P`$, $`\Lambda^*`$, $`\nu_P`$ and $`\nu_S`$ (the names up to $`\Lambda_\varepsilon`$ are now proved, [PINS.md](PINS.md) §3; the name of $`\Theta_P`$
  is now proved, [FANFREE.md](FANFREE.md) §10.4; $`\nu_S`$ is now
  described exactly, its name is a conjecture, [BREAK.md](BREAK.md) §2, reduced in §7.3; lower bounds for $`\Lambda^*`$ and $`\nu_P`$ that match the conjectures of §3 are now proved as a transfer, [THETA.md](THETA.md) §1; now the names of $`\Lambda^*`$ and $`\nu_P`$ are proved, [THETA.md](THETA.md) §9.1).
- FRAG2 beyond $`\nu_S`$: several bases that are not $`\upsilon`$-points at once (FRAG-E), and nested cut data.
- $`C^*_3`$: the upper half (an ordinal analysis of the generated structure), the lower half $`m_3 \ge \psi_{\Omega_1}(\varepsilon_{I_0+1})`$,
  and Conjecture CH. In $`R_2^C`$ the bottoms of chains are now characterized (Theorem CP3, [COVER.md](COVER.md) §1), but not located. An upper bound needs only one $`\lt_2`$-pair below it with one more point
  between (Lemma CRIT, [COVER.md](COVER.md) §6.2), but no InaccPsi term is proved to bound $`c_0`$.
- The order statement S for the converter above $`V_3`$ (the 26 undecided neighbour pairs of the sample are now proved, [FANFREE.md](FANFREE.md) §1; the step below SRO is proved for every $`n`$ on 459 of the 3,166 sample matrices, [FANFREE.md](FANFREE.md) §7.1, now on 1,987, [THETA.md](THETA.md) §3, then on 2,330, [THETA.md](THETA.md) §9.3, then on 2,526, [SHIFT.md](SHIFT.md) §3).
