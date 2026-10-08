[← Back](README.md) | [English](RESTARTS.md) | [Japanese](RESTARTS-ja.md)

# $`R_2^+`$ above $`\upsilon_{\omega^3}`$: Lemma FRAG, base changes for $`\le_2`$, and the restart blocks

This page continues §3 of [README.md](README.md). The status words are the same as there: **proved** means that an
independent referee found the result proved with no fatal or blocking point. Every result on this page is from
2026-10 and had **1 review** unless a count is given. A result marked **outline** was found "proved (outline), not
refuted" by its referee; it is not counted as proved. The results above $`\Xi_\omega`$ (exact reaches, the end of the
skeleton, the least chain of length 3) are on the third page [REACHES.md](REACHES.md), and those beyond $`\Lambda_\varepsilon`$
(relativized pins, the reaches up to $`\Theta_A`$, the names of all $`\upsilon`$-points up to $`\Lambda_\varepsilon`$) on the fourth page
[PINS.md](PINS.md), and those where the skeleton ends, with the levels of nested pairs above it, on the fifth page [BREAK.md](BREAK.md), and the results by covering minimality, and the
level-0 description of $`R_2^S`$ at every countable ordinal, on the sixth page [COVER.md](COVER.md), and the eighth to tenth rounds on the seventh page [FANFREE.md](FANFREE.md), and the eleventh and twelfth on the eighth page [VEBLEN.md](VEBLEN.md).

**Notation.** $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$. The reach of a point $`\alpha`$ is
$`\mathrm{lh}(\alpha) = \max\{\gamma : \alpha \le_1 \gamma\}`$. A restart index is a nonzero multiple $`\lambda`$ of $`\omega^2`$. Write
$`\lambda = \lambda_0 + \omega^e`$ (the last term of the Cantor normal form, $`e \ge 2`$) and call $`c(\lambda) = -1 + e`$ the offset
($`e - 1`$ for finite $`e`$, $`e`$ for infinite $`e`$). The restart is $`\rho_\lambda = \upsilon_\lambda`$, the pairs above it are
$`\tau^\lambda_j = \upsilon_{\lambda+\omega j}`$ and $`\delta^\lambda_j = \upsilon_{\lambda+\omega j+1}`$ ($`j \ge 1`$), and $`\delta_\lambda = \delta^\lambda_1`$ is
the top of its first block. $`\Xi_1 \lt \Xi_2 \lt \cdots`$ are the nonzero fixed points of $`\iota \mapsto \upsilon_\iota`$, and
$`\Xi_\omega = \sup_n \Xi_n`$. Write $`c^*(\lambda) = c(\lambda)`$ for $`\lambda \lt \Xi_\omega`$ and $`c^*(\Xi_\omega) = \Xi_\omega + 1`$.

## 1. Lemma FRAG (proved)

**Theorem FRAG** (finite form). Let $`\kappa`$ be a $`\upsilon`$-point that is an $`\varepsilon`$-number, and let
$`b_1 \lt \cdots \lt b_m`$ and $`c_1 \lt \cdots \lt c_m`$ be $`\upsilon`$-points above $`\kappa`$. For every finite set $`F`$ of ordinals
below $`\kappa`$ or in the segments of the $`b_k`$ (with their parameters) there is a map $`\Psi`$ on $`F`$ that is the
identity below $`\kappa`$, sends $`b_k`$ to $`c_k`$ and the segment of $`b_k`$ into that of $`c_k`$, keeps
$`0, +, \le, \le_1`$ of $`R_1^+`$ in both directions, and sends $`\upsilon`$-points to $`\upsilon`$-points and other ordinals to
other ordinals.

Proof outline. Push the top segment of each $`b_k`$ down, by Wilken's base change $`\pi_{\beta_k, b_k}`$, into
$`(\beta_k, \beta_k^+)`$, where $`\beta_k`$ is an $`\varepsilon`$-number inside the segment of $`b_{k-1}`$ (Lemma COMP). Inside that
interval the old parameters become ordinary subterms (Wilken, APAL 145 (2007) 130–161, Lemma 6.10). After $`m-1`$
steps everything lies in the segment of $`b_1`$; one base change moves it to $`c_1`$; then the steps are undone on
the side of the $`c_k`$. Each step keeps $`\lt, +, \le_1`$ in both directions (Lemma ST, from Wilken, APAL 145 (2007)
162–175, Cor 5.7, Lemma 4.4, Thm 5.3). The key point, checked by the referee: §4 of that paper allows any base in
$`\{1\} \cup E`$, so these results hold at the bases $`\beta_k`$, which are not $`\upsilon`$-points. Lemma R: the closure set is
finite. The $`\le_1`$ part covers every kind of pair (cases D1–D4).

The earlier review of the order proof below $`V_3`$ (in
[R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md)) accepted FRAG only as a sketch, and that sketch used a lemma that was
checked only by reading. The new proof does not use it. The referee checked every citation against the paper
texts and every case: no fatal or blocking point, five wording points.

**Lemmas RS and RS$`^h`$.** $`\rho_h \le_1 \delta^h_1 + 1`$ in $`R_2^S`$ for every $`h \ge 1`$, where
$`\rho_h = \upsilon_{\omega^2 h}`$ (proved, given the earlier refereed block results). So
$`\mathrm{lh}(\rho_h) = \delta^h_1 + 1`$.

**What now holds.** Every result that was "proved given FRAG" is proved:

- Theorem B′′ in full and Theorem EQB′′ for all pairs: $`R_2^C = R_2^S`$ below $`\upsilon_{\omega^3}`$.
- Theorem S below $`V_3 = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0)`$: $`\Phi_3`$ keeps the order on all standard
  matrices below $`V_3`$, and $`\iota(\Phi_3(M)) = \mathcal{T}_3(M)`$ (the order proof 1 review, FRAG 1 review).
- Theorem CORE-S up to $`\upsilon_{\omega^3}`$, and $`\beta_0 \ge \upsilon_{\omega^3}`$.
- The six minor points of the earlier review: three repaired, one covered by Lemma DIAG′, one fixed, one void.

Checks (each run under 60 s, 0 failures): 20,239 random configurations with 1 to 6 bases; 10,573,114 pairs for order
and $`+`$; 836,413 pairs for $`\le_1`$ inside a segment; three planted bugs were all caught. The referee's runs with new
seeds: about 1.9 million pairs, 0 failures. These runs test a program model of Wilken's terms, not $`R_1^+`$ itself.

**Conjecture** (checked, not used): the map of the proof does not depend on the choice of the $`\beta_k`$. Now proved: the map
equals a substitution map (FRAG-SUBST, [BREAK.md](BREAK.md) §4, 1 review).

## 2. Base changes that keep $`\le_2`$ (Theorem FRAG2)

$`R_2^+`$ is **skeletal** on a set $`Y`$ if every point of $`Y`$ that is not a $`\upsilon`$-point has its $`R_1^+`$ reach, and every
$`\lt_2`$-pair is $`(\upsilon_\xi, \upsilon_{\xi+1})`$. Write $`\mathrm{cap}(u) = \mathrm{lh}(u)`$.

- **Theorem FRAG2** (proved; it uses FRAG). Let $`\Psi`$ be a map of FRAG and $`Y`$ finite with $`R_2^+`$ skeletal on
  $`Y \cup \Psi[Y]`$. Then $`\Psi`$ keeps $`0, +, \le, \le_1, \le_2`$ on $`Y`$ if and only if for each $`\upsilon`$-point $`u \in Y`$ and
  each $`z \gt u`$ in $`Y`$: (C1) $`z \le \mathrm{cap}(u) \Leftrightarrow \Psi z \le \mathrm{cap}(\Psi u)`$, and (C2)
  $`u \lt_2 z \Leftrightarrow \Psi u \lt_2 \Psi z`$. So the maps that keep $`\le_2`$ are fixed by the reach and pair facts that $`Y`$
  sees, not by the indices alone. Cor. FRAG2-D gives index conditions for the whole domain below $`\upsilon_{\omega^3}`$.
  With one base no FRAG is needed (Cor. FRAG2-1). The referee notes that the theorem holds for every map that
  keeps $`0, +, \le, \le_1`$ of $`R_1^+`$, keeps $`\upsilon`$-points and fixes a lower segment.
- **Lemma SK3** (proved, no FRAG). $`R_2^S`$ and $`R_2^C`$ are skeletal below $`\upsilon_{\omega^3}`$.
- **NAIVE-FAIL** (proved). Wilken's rule for pure $`R_2`$ "move a limit base to a limit base" (Wilken 2020, p. 434) is
  false in $`R_2^+`$: $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$, but $`\upsilon_{\omega^2}`$ has no $`\lt_2`$-successor. His compressing map does not
  keep $`+`$.
- **Lemma PAIR-SK** (proved in $`R_2^S`$, no FRAG). A sufficient condition for $`\upsilon_\lambda \lt_2 \upsilon_{\lambda+1}`$, shown with one
  base change.
- **Above $`\upsilon_{\omega^3}`$** ($`R_2^S`$). Write $`\delta_O = \upsilon_{\omega^3+\omega+1}`$. The first restart block of
  $`\upsilon_{\omega^3}`$ and TOP$`^{\omega^3}`$ (no FRAG); and **Theorem RS$`^{\omega^3}`$**:
  $`\mathrm{lh}(\upsilon_{\omega^3}) = \delta_O + 2`$. This is the reach "top of its block + 2" that the program gives. All proved.
- **Corollary 6.4** (proved). $`R_2^S`$ is skeletal below $`\delta_O + 3`$. The first point $`\nu_S`$ where $`R_2^S`$ stops being
  skeletal is countable and at most the top of any chain of length 3; by §3 it is at least $`\upsilon_{\Xi_\omega+\omega^2}`$.

Not proved: the remark that FRAG2 reduces Lemma RS$`_\lambda`$ of §3 for every $`\lambda`$ (the choice of the target restart,
and the cap of a target with a moved offset, are not shown; RS$`_\lambda`$ itself is now proved another way, [REACHES.md](REACHES.md) §1); the aside "without FRAG, an isomorphism of the whole
domain iff RS fails" (its "if" direction needs FRAG; it was not checked again).
Conjectures: **CAP**, $`\mathrm{lh}(\upsilon_{\omega^2\eta}) = \upsilon_{\omega^2\eta+\omega+1} + (1 + \mathrm{logend}(\eta))`$ for $`\eta \ge 1`$
(the program agrees on 11 restarts, among them "top + $`\omega`$" at $`\upsilon_{\omega^\omega}`$; by Theorem OFF-V of [REACHES.md](REACHES.md)
§1 it holds at every restart of level 0 and fails at $`\Xi_\omega`$); **FRAG2-GEN**, beyond the
skeleton FRAG2 must also move $`\varepsilon`$-bases that are not $`\upsilon`$-points, with Wilken's $`\iota_{\tau,\alpha}`$ (partly proved,
[REACHES.md](REACHES.md) §4). $`\nu_S`$ is now known exactly: it is the top of the least $`\lt_2`$-pair with another $`\lt_2`$-pair nested inside (Theorem FIRST-PAIR,
1 review), and in $`R_2^C`$ the first non-skeletal point $`\nu_C`$ is $`\le \nu_S`$ and $`\gt \nu_P`$ (Theorem NU-CT, 1 review), both on
[BREAK.md](BREAK.md) §2. Its name is a conjecture; it is now equivalent to three statements about $`\upsilon`$-indices (1 review, [BREAK.md](BREAK.md) §7.3).
In $`R_2^C`$ the shape part is proved: $`\nu_C = \upsilon^2_{\omega+1}`$, from $`o_2 = \omega`$ (Theorem O$`^C`$, 1 review, [BREAK.md](BREAK.md) §8.1).
In $`R_2^C`$ NOLIM holds too (1 review, [COVER.md](COVER.md) §3 and §5.1), and $`\nu_C = \nu_S`$ is equivalent to NOLIM and $`o_2 = \omega`$ in $`R_2^S`$ (1 review, [COVER.md](COVER.md) §3).
It is also equivalent to one $`\Sigma_2`$ statement, $`x_2 \lt_2^S \nu_C`$, inside the structure that $`R_2^S`$ and $`R_2^C`$ share below $`\nu_C`$ (1 review, [COVER.md](COVER.md) §6.3).
The points $`\upsilon^2_n`$ and $`x_2`$ of level 2 are fixed points of $`\iota \mapsto \upsilon_\iota`$ (1 review), and the reaches of restarts correspond between
the segments of level 2 on the initial part of each segment (outline only; [FANFREE.md](FANFREE.md) §3). Now (1 review) this is proved below the first
limit of "critical" indices of each segment, and the reach of every restart below $`\nu_C`$ is known except at limits of critical indices ([FANFREE.md](FANFREE.md) §7.3).
Then (1 review) the reaches are known up to offset $`\rho^\rho`$ and the correspondence holds on a larger part, but the reduction always needs long restarts, where no closed
form of the reaches applies, so $`\nu_C = \nu_S`$ stays open ([FANFREE.md](FANFREE.md) §10.3). Working with the $`\Sigma_2`$ statement directly (1 review), every
extension above the copy, the long restarts included, is matched, but a local part with a fixed finite set below the copy is left, so
$`\nu_C = \nu_S`$ is still open ([VEBLEN.md](VEBLEN.md) §4). With that set held fixed, the reduction fails on the zone where the copy is known
exactly ([VEBLEN.md](VEBLEN.md) §11).
In $`R_2^S`$, at every countable ordinal, every pair is a standard pair or joins two restarts, so FRAG2 holds in the weaker form
"every pair joins two $`\upsilon`$-points" (Theorem SKEL$`^\infty`$, 1 review, [COVER.md](COVER.md) §5.1; before, below $`T_\omega`$ and at outline level only).

Checks (0 failures): 25,238 maps on 4,144 patterns in a model (dropping C1 or C2 gives mismatches); 35,104 moved
standard matrices and 5,384,652 pairs in the program `phi3def2`, whose $`\le_1`$ and $`\le_2`$ facts change exactly where
FRAG2 predicts; 2,591 patterns moved to the block of $`\upsilon_{\omega^3}`$ with no change. The referee's re-runs with a
new seed (12,539 new matrices, 1,595,592 pairs): 0 failures. The referee notes that the model test repeats the proof
and that the program is not an independent oracle.

## 3. The restart blocks up to $`\Xi_\omega`$ (Theorem BLK$`^\Xi`$)

**Theorem BLK$`^\Xi`$** (proved, in $`R_2^S`$ and $`R_2^C`$, no FRAG). For every $`\alpha \lt \upsilon_{\Xi_\omega+\omega^2}`$:

- (i) the $`\lt_2`$-pairs with left end below $`\upsilon_{\Xi_\omega+\omega^2}`$ are exactly $`(\tau^\lambda_j, \delta^\lambda_j)`$, with
  $`\lambda = 0`$ or a restart index, and $`j \ge 1`$;
- (ii) a restart $`\rho_\lambda`$ ($`\lambda \le \Xi_\omega`$) has no $`\lt_1`$-predecessor and no $`\lt_2`$-successor, and
  $`[\rho_\lambda, \delta_\lambda] \subseteq \{\gamma : \rho_\lambda \le_1 \gamma\} \subseteq [\rho_\lambda, \delta_\lambda + c^*(\lambda)]`$;
- (iii) every other $`\alpha`$ lies in a block with top $`d`$, and $`\alpha \le_1 \gamma`$ holds exactly for the $`\gamma \le d`$ with
  $`\alpha \le_1 \gamma`$ in $`R_1^+`$.

The upper end in (ii) is **Lemma TOP$`_\lambda`$** (proved, both structures). It works because the restarts shortly before
$`\lambda`$ have smaller offsets; a fixed extra parameter handles cases such as $`\upsilon_{\omega^3\cdot 2}`$. Its case
$`\lambda = \omega^3`$ is TOP$`_3`$, which was the blocker of the core bound in $`R_2^C`$. An earlier note said that this
argument cannot bound a reach "top + $`\omega`$"; that was wrong ($`\omega`$ is a fixed parameter). **Theorem EQB$`^\lambda`$**
(proved): $`R_2^C`$ and $`R_2^S`$ agree on $`[0, \upsilon_{\lambda+\omega^2})`$ except possibly on the pairs
$`(\rho_\mu, \delta_\mu + \xi)`$, $`0 \lt \xi \le c^*(\mu)`$, where $`S \Rightarrow C`$ holds.

**Lemma RS$`_\lambda`$** (the lower end, $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^*(\lambda)`$): the first sketch was not proved (its
choice of the target restart fails when $`e = e' + 1`$, for example $`\lambda = \omega^4`$). It is now **proved** for every
$`\lambda \le \Xi_\omega`$, in $`R_2^S`$ and $`R_2^C`$, by two independent papers (2 reviews; [REACHES.md](REACHES.md) §1). So the
exceptional pairs of EQB$`^\lambda`$ below agree too.

- **Theorem CORE-C$`^\Xi`$** (proved, no FRAG). Every ordinal $`\le \Xi_\omega`$ is in $`\mathrm{Core}(R_2^C)`$ (by the caps and
  Carlson 2009, Thm 14.14). Before, this was known up to $`\upsilon_{\omega^3}`$. The referee notes that the caps give
  $`[0, \upsilon_{\Xi_\omega+\omega^2})`$. Now extended to $`[0, \Lambda_\varepsilon)`$ and $`[0, \rho_{\Theta_P})`$ ([REACHES.md](REACHES.md) §2), and to
  $`[0, \rho_{\Theta_A+\omega^2})`$ ([PINS.md](PINS.md) §2).
- **Corollary** (proved). $`\min C^*_3 \ge \upsilon_{\Xi_\omega+\omega^2}`$ and $`m_3 \gt \Xi_\omega`$, without FRAG. Now $`m_3 \ge \Lambda_\varepsilon`$
  ([REACHES.md](REACHES.md) §5).

Checks: on the 25 restart matrices with a prediction, from $`V_3`$ to $`\Xi_\omega`$, the reach of the point in the
program is $`\delta + c^*(\lambda)`$; 79 of 79 certificates found and replayed (19 consecutive restarts, 60 pairs
$`M[N] \lt M`$), 0 of 19 in the reversed direction. The referee: 559 restarts below $`\omega^{\omega^2}`$ for the offset lemma
(0 violations), 11 new restart matrices (reach $`\delta + c(\lambda)`$ in all), 10 of 10 certificates replayed, Lean names
check green.

## 4. Names up to the first fixed point (Theorem T+)

Let $`g(x) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot x)`$ and $`s_1 = \sup_n g^n(0)`$.

- **Theorem T+** (proved, 2 reviews; the second proof is Theorem GEN of [PINS.md](PINS.md) §3, which names every
  $`\upsilon`$-point). $`\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ for every $`\eta \lt s_1`$, and
  $`\Xi_1 = s_1`$. The old bound $`\Gamma_0`$ of T-UP came only from the hypothesis (HA), and (HA) holds whenever
  $`\eta \lt g(\eta)`$.
- $`s_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1})`$ (proved, 3 reviews; [REACHES.md](REACHES.md) §2, Theorem T++). This is
  the name of row 26 of the table in README §6.
- So **Wilken's claim holds on $`[0, \Xi_1]`$ in $`R_2^C`$**, both halves: every ordinal there is in the core and is the
  value of an InaccPsi normal form with collapse arguments below $`\Omega_\omega + \omega^{\theta+\Omega_1}`$ (Lemma IS).
- Upper names just above $`\Xi_1`$, by Lemma REL: $`\upsilon_{\Xi_1+1+\eta} \le \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1} + \theta\cdot(1+\eta))`$
  for $`\eta \lt \Gamma_0`$ (proved). Now an equality for every $`\eta`$ with $`\Xi_1 + 1 + \eta \lt \Xi_2`$, and the claim holds up to
  $`\Phi_1`$ ([REACHES.md](REACHES.md) §2), and now up to $`\Lambda_\varepsilon`$ ([PINS.md](PINS.md) §3).

## 5. Toward a structure theorem (Wilken 2021, Thm 4.2)

Wilken's Thm 4.2 describes $`\le_1`$ and $`\le_2`$ of pure $`R_2`$ below the least $`\le_2`$-chain of length 3. Its statement,
proof map and tools were written out (cited; the referee checked them against the paper). The two main tools,
translations and base change of tracking-chain indices, behave differently with $`+`$:

- broken by $`+`$: the translation maps, the "multiples" form of values, the $`R_1`$ formula inside his $`\mathrm{dp}`$;
- changed: base change acts on the ordinals, not on the indices;
- kept: his Lemma 1.7 and Prop 1.6.

The literal copy "$`\varepsilon_0\cdot\iota \mapsto \upsilon_\iota`$" of pure $`R_2`$ is false: at $`\lambda = \omega^\omega`$ pure $`R_2`$ has the
reach $`\delta + \omega + 1`$, while $`R_2^+`$ has at most $`\delta + \omega`$ (§3).

Proved small lemmas: **L17-1** (Wilken 2021, Lemma 1.7(1), for $`R_2^S`$ and $`R_2^C`$); **C-3.1** (his Lemma 3.1 in
$`R_2^C`$, after a one-line fix); **CORE-MIN** ($`\kappa_C`$ has no $`\lt_1`$-predecessor and no $`\lt_2`$-successor);
**PRED2-FIN** (inside the core every set of $`\lt_2`$-predecessors is finite; uses Theorem CC); **TOP-GEN** (one lemma
that caps the reach of a point, both structures).

**Outline:** Theorem BLK$`^F`$-UP (the pairs, the block caps and the upper bound of the restart reaches below
$`\upsilon_{\Xi_1}`$, in $`R_2^S`$). The referee found it not refuted but did not check all steps line by line. It is
covered by Theorem BLK$`^\Xi`$ of §3, which is proved in both structures. The review found one blocking point, against
the claim that this file removes the blocker TOP$`_3`$ in $`R_2^C`$ (it proves only the $`R_2^S`$ form); TOP$`_3`$ in $`R_2^C`$ is
proved by Lemma TOP$`_\lambda`$ of §3 instead.

**Conjecture 42+.I** (below $`\upsilon_{\Xi_1}`$, in InaccPsi terms through Theorem T+): the only $`\lt_2`$-pairs are, for suitable $`A`$,
$`\psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1}) \lt_2 \psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1} + \theta)`$; inside each block
$`R_2^+`$ is $`R_1^+`$ cut at the top; a restart $`\upsilon_\lambda`$ has reach exactly $`\delta_\lambda + (-1 + \mathrm{logend}\,\lambda)`$. The pair
and block parts are now proved (§3), and so is the exact reach: below $`\upsilon_{\Xi_1}`$ the conjecture is a theorem
([REACHES.md](REACHES.md) §2). **Part II** (from $`\upsilon_{\Xi_1}`$ to
$`\psi_{\Omega_1}(I_\omega)`$): only its shape is known; it needs operators that no available paper defines.

## 6. Open

The open problems above $`\Xi_\omega`$ are listed in [REACHES.md](REACHES.md) §7. Of the earlier list: Lemma RS$`_\lambda`$, the
offsets beyond $`\Xi_\omega`$ (up to $`\Lambda_\varepsilon`$) and the equality for $`s_1`$ are now proved ([REACHES.md](REACHES.md) §1–2). Still open here:

- The order statement S for the converter above $`V_3`$ (the reaches are now known up to $`\Lambda_\varepsilon`$; the order proof for
  the new prefixes is missing). The 26 undecided neighbour pairs of the sample above $`V_3`$ are now proved ([FANFREE.md](FANFREE.md) §1), and the step below SRO is proved for every $`n`$ on 459 of the 3,166 sample matrices ([FANFREE.md](FANFREE.md) §7.1), now on 1,987 ([THETA.md](THETA.md) §3), then on 2,330 ([THETA.md](THETA.md) §9.3), then on 2,526 ([SHIFT.md](SHIFT.md) §3), then on 2,589 ([SHIFT.md](SHIFT.md) §8.3), and now on 3,113 ([SHIFT3.md](SHIFT3.md) §1.3).
- The core of $`R_2^S`$ above $`\upsilon_{\omega^3}`$ (Theorem CORE-S stops there).
