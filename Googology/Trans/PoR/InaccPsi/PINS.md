[← Back](README.md) | [English](PINS.md) | [Japanese](PINS-ja.md)

# $`R_2^+`$ beyond $`\Lambda_\varepsilon`$: relativized pins, reaches up to $`\Theta_A`$, names up to $`\Lambda_\varepsilon`$, and the bottom of a chain of length 3

This page continues [REACHES.md](REACHES.md). The status words are those of [README.md](README.md) §3: **proved**
means that an independent referee found the result proved with no fatal or blocking point. All results on this
page are from 2026-10; they come from four papers, each refereed once. "1 review" means one referee. "2 reviews"
means that two independent papers proved the result and each paper was refereed once. A statement that its referee
found not proved is listed under **Not proved**, even when the rest of its paper is proved. None of the four papers
uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006). The next four rounds are on the fifth page
[BREAK.md](BREAK.md), the fifth to seventh rounds on the sixth page [COVER.md](COVER.md), and the eighth to tenth on the seventh page [FANFREE.md](FANFREE.md), and the eleventh and twelfth on the eighth page [VEBLEN.md](VEBLEN.md); they change some statuses here, as marked.

**Notation.** As on [REACHES.md](REACHES.md). For a $`\upsilon`$-point $`\tau`$, $`\tau^\infty`$ is the least $`\upsilon`$-point above
$`\tau`$, and $`\mathrm{seg}(\tau) = [\tau, \tau^\infty)`$. For a restart index $`\lambda`$: $`\sigma_\lambda = \upsilon_{\lambda+1} = \rho_\lambda^\infty`$ and
$`\sigma'_\lambda = \upsilon_{\lambda+2}`$. $`\pi_{\sigma,\tau}`$ is Wilken's base change (APAL 145 (2007) 130–161, Def 5.1), and
$`\pi_\mu = \pi_{\rho_\mu,\rho_\lambda}`$. $`c^+`$ is the formal offset of [REACHES.md](REACHES.md) §1 (Theorem EXACT), $`\Theta_P`$ the least
$`\lambda`$ with $`c^+(\lambda) \ge \varepsilon_{\rho+\omega}`$, and $`\Lambda^*`$, $`\nu_P`$ are as in [REACHES.md](REACHES.md) §3. New:
$`\Theta_1`$ is the least restart index $`\lambda`$ at which $`c^+(\lambda)`$ is undefined (the offsets have used up $`\mathrm{seg}(\rho_\lambda)`$);
$`c^\#`$ continues $`c^+`$ into $`[\sigma, \varepsilon_{\sigma+\omega})`$ (the transport sends $`\sigma_\lambda`$ to $`\sigma_\mu`$ and keeps $`+`$,
$`x \mapsto \omega^x`$ and $`\varepsilon`$); $`\Theta_A`$ is the least $`\lambda`$ at which $`c^\#(\lambda)`$ is undefined.

## 1. Relativized patterns of $`R_1^+`$

Wilken (APAL 145 (2007) 162–175, p. 174) announces, for a paper that we do not have, three things: another proof
that the core of $`R_1^+`$ is the least $`\alpha`$ with $`\alpha \le_1 \infty`$, relativized patterns, and uniform elementary
recursive assignments between ordinals and patterns. One paper rebuilds all of it except "elementary recursive".

A $`\tau`$-pattern is a pair $`(A, B)`$ of finite sets with $`A \subseteq \tau`$ (the parameters) and $`\tau \in B \subseteq [\tau, \infty)`$. A
$`\tau`$-covering keeps $`\le`$, $`+`$ and $`\le_1`$ (forward); it may raise the parameters ($`h(a) \ge a`$ on $`A`$, $`h(\tau) \ge \tau`$).
$`\mathrm{Core}^\tau`$ is the union of the sets $`B`$ of the $`\tau`$-isominimal patterns.

- **Theorem RC-PIN** (proved, 1 review; $`\tau \in \{1\} \cup E`$). Every $`z \in [\tau, \tau^\infty)`$ is pinned by a finite
  $`\tau`$-pattern: every $`\tau`$-covering of it, also one that raises the parameters, has $`h(z) \ge z`$. The pins are already
  inside Wilken's proof of his Thm 5.3 (Claims 5.5(a)(ii) and 5.6). The case of one segment ($`\tau`$ a $`\upsilon`$-point) was
  proved independently in a second paper (Lemma RP, 1 review), so that case has **2 reviews**.
- **Theorem RC** (proved, 1 review). For every $`\tau \ge 1`$: $`\mathrm{Core}^\tau = \{\tau\text{-pinned points}\} = [\tau, \tau^\infty)`$. For
  $`\tau \in \{1\} \cup E`$ this is $`T^\tau \cap [\tau, \Omega_1)`$.
- **Corollary CORE1** (proved, 1 review). $`\mathrm{Core}(R_1^+) = [0, \upsilon_1)`$, without Carlson 2001, Thm 5.12 (only the
  definition of the core is used). This is the first item of Wilken's announcement.
- **Theorem U** (proved, 1 review). Let $`\sigma \lt \tau`$ be $`\upsilon`$-points and $`z \in \mathrm{seg}(\tau)`$. Every map that fixes the
  parameters, keeps $`\le`$ and $`+`$, sends $`\tau`$ to $`\sigma`$ and keeps the $`\le_1`$-facts above $`\tau`$ has $`h(z) \ge \pi_{\sigma,\tau}(z)`$.
  Also COMP-π ($`\pi_{\sigma,\tau} = \pi_{\sigma,\sigma'} \circ \pi_{\sigma',\tau}`$) and MON-π are proved.
- **Theorem UNIF** (proved, 1 review). $`\pi_{\sigma,\tau}`$ maps every $`\tau`$-isominimal pattern to a $`\sigma`$-isominimal one, as an
  isomorphism of $`R_1^+`$. **The assignments** $`z \mapsto P^\tau(z)`$ and $`(P, b) \mapsto \nu^\tau(P, b)`$ (the least $`h(b)`$ over the
  strict $`\tau`$-coverings $`h`$ of $`P`$) are inverse to each other and commute with $`\pi`$ (proved, 1 review, for strict
  coverings). **CL-UNIF** (proved, 1 review): the closure $`C_\tau(z)`$ of $`\{0, \tau, z\}`$ under components, $`\mathrm{lh}`$ and the
  bar operation commutes with $`\pi`$.
- **Not proved.** That UNIF is onto (a $`\tau`$-copy of the pulled-back pattern can leave the domain of $`\pi`$); that
  $`\pi[P^\tau(z)]`$ serves as $`P^\sigma(\pi z)`$ against coverings that raise the parameters; that $`C_\tau(z)`$ is a $`\tau`$-isominimal pin
  pattern as stated (the cited theorem uses the coverings of Carlson–Wilken, JSL 77 (2012), not these). The last point is now
  proved by Theorem EXPL ([BREAK.md](BREAK.md) §4, 1 review).
- **Open.** Whether $`C_\tau(z)`$ is always finite (CL-FIN), so whether the assignments are elementary recursive. As
  defined they are not effective. Now CL-FIN is proved ([BREAK.md](BREAK.md) §4, 1 review); "elementary recursive" is only an outline. The referee notes that Carlson–Wilken 2012, §3 (Def 3.6, Thm 3.9(1)) already has a
  relativized pattern theory inside the core; Theorem RC is the analogue for this weaker notion, for every $`\tau`$ and
  above the core.

## 2. Exact reaches up to $`\Theta_A`$

- **Lemma PIN\*** (proved, 1 review; no FRAG), found independently as **IMG$`^T`$** (1 review), so **2 reviews**. In every copy
  or covering $`h`$ used for an upper bound at a restart $`\lambda`$ ($`h`$ fixes the parameters below $`\rho`$, $`h(\rho) = \rho_\mu`$):
  $`h(c) \ge \pi_\mu(c)`$ for every $`c \in \mathrm{seg}(\rho)`$ whose parameters are fixed, not only for $`c \lt \varepsilon_{\rho+\omega}`$ (Lemma PIN).
  **CAP-PIN**: $`h(\sigma_\lambda)`$ is a $`\upsilon`$-point $`\ge \sigma_\mu`$. **PIN-A**: the same for terms over $`\sigma`$ up to $`\varepsilon_{\sigma+\omega}`$.
- **Theorem EXACT-1** (proved, 2 reviews). For every restart index $`\lambda \lt \Theta_1`$, in $`R`$:
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^+(\lambda)`$. The upper bound uses no FRAG; the lower bound uses FRAG. Also
  $`c^+(\Theta_P) = \varepsilon_{\rho+\omega}`$ (1 review) and $`\Theta_P \lt \Theta_1 \le \Lambda^*`$ (2 reviews).
- **Theorem EXACT-A** (proved, 1 review). For every $`\lambda \lt \Theta_A`$, in $`R`$: $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^\#(\lambda)`$. At
  $`\Theta_1`$: $`\mathrm{lh}(\rho_{\Theta_1}) = \delta + \sigma`$ (the lower bound has 2 reviews). At $`\Theta_A`$:
  $`\delta + \varepsilon_{\sigma+\omega} \le \mathrm{lh}(\rho_{\Theta_A}) \le \delta + \sigma'`$. The lower bounds use FRAG and Lemma FRAG-T (the map of FRAG
  commutes with $`+`$, $`x \mapsto \omega^x`$ and $`\varepsilon`$ on the offset terms; proved given FRAG).
- **Lemma ATTAIN** (proved, 1 review; combinatorial, no FRAG). Every value $`t`$ of $`c^+`$ or $`c^\#`$ is attained exactly, at the
  least $`\lambda`$ with $`c^+(\lambda) \ge t`$. So $`\Lambda_\Gamma \lt \Lambda_\varepsilon \lt \Theta_P \lt \Theta_1 \lt \Theta_A \lt \Lambda^*`$.
- **$`R_2^C`$ up to $`\rho_{\Theta_A+\omega^2}`$** (proved, 1 review). Theorem EQB-A: on $`[0, \rho_{\Theta_A+\omega^2})`$, $`R_2^C`$ has the pairs,
  blocks and caps of $`R_2^S`$, and equals $`R_2^S`$ there (using FRAG) except possibly on the pairs $`(\rho_{\Theta_A}, \delta + \xi)`$
  with $`\varepsilon_{\sigma+\omega} \lt \xi \le \sigma'`$. So $`\beta_0 \ge \rho_{\Theta_A}`$. Corollary CORE-C$`^A`$ (no FRAG):
  $`[0, \rho_{\Theta_A+\omega^2}) \subseteq \mathrm{Core}(R_2^C)`$; the part $`[0, \rho_{\Theta_1})`$ has 2 reviews. The hypothesis HC of
  [REACHES.md](REACHES.md) §3 (the $`R_2^C`$ reach of a restart is at most its $`R_2^S`$ reach) holds for every restart index
  $`\lambda \lt \Theta_A`$, using FRAG (the referee's corrected form, see below).
- **Reaches by reflection** (proved, 1 review). **INDEX**: a copy at a restart sends the $`\upsilon`$-points of every block
  that it carries with their witnesses to $`\upsilon`$-points at or above their index shift. **TOP-FLAT$`_0`$** (no FRAG) and
  **REACH$`_0`$** (using FRAG): if the least point $`y_0 \ge \delta`$ that is not reflected lies in FLAT$`_0`$ (sums of $`\upsilon`$-points
  of $`[\rho, \delta_j]`$, points of $`\mathrm{seg}(\rho)`$ and constants below $`\rho`$), then $`\mathrm{lh}(\rho_\lambda) = y_0`$. This covers the
  program's reaches of the form $`\delta_{n+1} + \tau_{n+1}`$. **TOP-FLAT$`_1`$** (one segment above $`\rho`$): proved given the
  lemmas LHPAR\* and CL-FIN, and now proved outright (Theorem EXPL, [BREAK.md](BREAK.md) §4).
- **Conditional** (proved, 1 review, given FRAG and the hypothesis H-RC: pins with index shift for every segment of the
  region). For every $`\lambda \le \Lambda^*`$ the reach of $`\rho_\lambda`$ is the supremum of $`y + 1`$ over the reflected points $`y`$, and
  $`\Lambda^*`$ is the least $`\lambda`$ that is fully reflected. H-RC was open beyond the first segment; it is now proved (Lemma PIN-S,
  [BREAK.md](BREAK.md) §4, 1 review), and it holds at every restart below $`\nu_S`$ ([SHIFT.md](SHIFT.md) §9.1), and over every region at a fixed index distance (MULTI-RC\*, [SHIFT2.md](SHIFT2.md) §1.1), and across every η-offset below $`\psi_{\Omega_2}(\Omega_2)`$ (MULTI-RC$`^U`$, §2.1 there), and below $`\psi_{\Omega_2}(\Omega_2^{\Omega_2})`$ (§3.1 there), and below $`\psi_{\Omega_2}(\varepsilon_{\Omega_2+1})`$ ([SHIFT3.md](SHIFT3.md) §1.1), and below $`\theta`$ (§2.1 there), and below $`\psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ ([SHIFT4.md](SHIFT4.md) §1.1, §1.4), and for the multipliers $`\zeta \ge \Omega_3`$ below the point $`\hat\zeta_2`$ of §2.2 there (§2.1, §2.2 there), and with long prefix restarts below $`\hat\zeta_\varepsilon`$ (MULTI-RC$`^L`$, [SHIFT5.md](SHIFT5.md) §1.1), and at every level (§2.2 there), and with moved lower parameters (MRC$`^{\mathrm{mv}}`$, [SHIFT6.md](SHIFT6.md) §1.2).
- **Not proved** (blocking point, one sentence): "HC holds on all of $`[0, \rho_{\Theta_A+\omega^2})`$". At $`\Theta_A`$ itself only the
  bounds above are known, and EQB-A allows $`R_2^C \ne R_2^S`$ there. No theorem uses the sentence. Now the reach at $`\Theta_A`$ is
  $`\delta + \varepsilon_{\sigma+\omega}`$, so HC holds at every $`\lambda \le \Theta_A`$ and $`R_2^C = R_2^S`$ on $`[0, \rho_{\Theta_A+\omega^2})`$ ([BREAK.md](BREAK.md) §4, 1 review).
- **Conjectures** (names checked): $`\Theta_P = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+\omega}})`$,
  $`\Theta_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$, $`\Theta_A = \psi_{\Omega_1}(\Omega_\omega + \varepsilon_{\theta+\omega})`$. The name of $`\Theta_P`$ is now proved (1 review, THETA-P,
  [FANFREE.md](FANFREE.md) §10.4). The name of $`\Theta_1`$ is now reduced to an open hull lemma (THETA1-RED, [VEBLEN.md](VEBLEN.md) §1), and then the names of $`\Theta_1`$ and $`\Theta_A`$ to one short open
  lemma on parameters (PAR-SAME, [VEBLEN.md](VEBLEN.md) §8; the proofs have a blocking gap without it). PAR-SAME is now proved, so both names are proved
  (THETA1 and THETA-A, 2 reviews, [THETA.md](THETA.md) §1).

## 3. Names of all $`\upsilon`$-points (Theorem GEN)

Let $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ and $`D = \{\eta \lt \Omega_2 : \eta \in \mathrm{Cl}(\Omega_\omega + \theta\cdot\eta, H(\eta))\}`$, the set of
$`\eta`$ for which $`\Omega_\omega + \theta\cdot\eta`$ is a normal argument. For a countable $`\eta`$: $`\eta \in D`$ iff $`\eta \lt H(\eta)`$.

- **Theorem GEN** (proved, 1 review). For every $`\eta \in D`$: $`H(\eta) = \upsilon_{1+\iota(\eta)}`$ with $`\iota(\eta) = \mathrm{otp}(D \cap \eta)`$.
  So the terms $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`\eta \in D`$, list the $`\upsilon`$-points in increasing order, but only those below
  $`\upsilon^* = \sup H[D]`$: the $`\upsilon`$-points are cofinal in $`\omega_1`$, so not all of them (correction, [BREAK.md](BREAK.md) §3; GEN-EXT
  extends the list to $`\eta \lt \Omega_\omega\cdot\omega`$, §2; now $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ is proved, 1 review, [THETA.md](THETA.md) §1). Proof:
  STEP and LOW-STEP at successors; CONT and one general hull-gap lemma at limits. It holds for all $`\eta \lt \Omega_2`$.
  Theorems T+, T++ and PHI are special cases, so T+ now has **2 reviews**, T++ **3** and PHI **2**.
- **Lemmas GAP\*, SUP, DOWN, RI** (proved, 1 review). RI: $`\iota(\eta)`$ is a restart index iff $`\mathrm{logend}(\eta) \ge 2`$, and a
  successor iff $`\mathrm{logend}(\eta) = 0`$.
- **Theorem NAME-V** (proved, 1 review; a conjecture in [REACHES.md](REACHES.md) §2). For countable $`g \ge 1`$ and $`\eta \in D`$:
  $`H(\eta)`$ is in the range of $`V_g`$ iff $`\mathrm{logend}(\eta) \ge \Omega_1\cdot g`$. If $`g, a \lt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot g}\cdot a)`$,
  then $`V_g(a) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot g}\cdot a)`$. So $`\Phi_1 = V_2(1) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$ and
  $`\Lambda_\Gamma = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1^2})`$; the $`\Gamma`$-points are the $`H(\Omega_1^{\Omega_1}\cdot\beta)`$. A second paper proved
  these names below $`\Lambda_\Gamma`$ independently (Theorem NAMES-Γ, 1 review: the terms $`\psi_{\Omega_1}(A)`$ with
  $`A = \Omega_\omega + \omega^{\theta+e_1} + \cdots + \omega^{\theta+e_m}`$, $`e_j \in [\Omega_1, \Omega_1^2)`$, list all fixed points of $`\iota \mapsto \upsilon_\iota`$
  below $`\Lambda_\Gamma`$, and $`\upsilon_{\psi_{\Omega_1}(A)+x} = \psi_{\Omega_1}(A + \theta\cdot x)`$ between them; also
  $`V_\omega(1) = \Theta_{add} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\omega^{\Omega_1+1}})`$). So the names $`V_g(a)`$ below $`\Lambda_\Gamma`$, and $`\Lambda_\Gamma`$
  itself, have **2 reviews**.
- **Theorem NAME-OFFSET** (proved, 1 review; a conjecture in [REACHES.md](REACHES.md) §2). For a restart index $`\lambda`$, let
  $`\eta_\lambda \in D`$ with $`\iota(\eta_\lambda) = \lambda`$, and $`e_\lambda = \mathrm{logend}(\eta_\lambda)`$. Then $`\lambda \lt \Lambda_\varepsilon`$ iff
  $`\eta_\lambda \lt \varepsilon_{\Omega_1+1}\cdot\omega`$, and in that case $`O(\lambda) = (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$, so in $`R`$
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$. Also $`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$, and the
  first restart with $`O = \varepsilon_{\rho+1}`$ is $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}})`$. This is the closed form of $`O`$ on all
  of $`[0, \Lambda_\varepsilon)`$. Below $`\Lambda_\Gamma`$ it has 2 reviews (NAMES-Γ gives the same offsets).
- So **Wilken's claim holds on $`[0, \Lambda_\varepsilon)`$ in $`R_2^C`$**, both halves (1 review; on $`[0, \Lambda_\Gamma]`$ 2 reviews): every
  ordinal there is in the core and is the value of an InaccPsi normal form with collapse arguments below
  $`\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1} \lt I_\omega`$. Before: $`[0, \Phi_1]`$. Now (1 review) on $`[0, \rho_{\Lambda'+\omega^2})`$ with
  $`\Lambda' = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\zeta_{\Omega_1+1}+1}})`$ ([FANFREE.md](FANFREE.md) §10.4), and now (1 review) on $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$ with
  $`\Lambda_{\mathrm{fp}} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2)+1})`$ ([VEBLEN.md](VEBLEN.md) §1), and now (1 review) on $`[0, \rho_{\Lambda_{\mathrm{fp}2}+\omega^2})`$ with
  $`\Lambda_{\mathrm{fp}2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2\cdot 2)+1})`$ ([VEBLEN.md](VEBLEN.md) §8).
- **Not proved, and false** (blocking point, statement only): the author's form "$`\lambda \lt \Lambda_\varepsilon`$ iff
  $`e_\lambda \le \varepsilon_{\Omega_1+1}`$". The referee's counterexample: $`\eta = \varepsilon_{\Omega_1+1}\cdot\omega + \omega^2`$ is in $`D`$ with $`e = 2`$, but
  $`\iota(\eta) \gt \Lambda_\varepsilon`$. The corrected form is the one above; no other result uses the false direction.
- **Conjecture NAME-OFFSET+.** The same offset formula for every restart with $`\eta_\lambda \lt \theta`$. Now proved (1 review) for
  $`e_\lambda \le \varepsilon_{\zeta_{\Omega_1+1}+1}`$, with $`\zeta_{\Omega_1+1}`$ the least fixed point of $`\alpha \mapsto \varepsilon_\alpha`$ above $`\Omega_1`$ (NAME-OFFSET-Z, [FANFREE.md](FANFREE.md) §10.4), and now
  for $`e_\lambda \le \psi_{\Omega_2}(\Omega_2) + 1`$, with $`\psi_{\Omega_2}(\Omega_2)`$ the least fixed point of $`\alpha \mapsto \Gamma_\alpha`$ above $`\Omega_1`$ (NAME-OFFSET-G, [VEBLEN.md](VEBLEN.md) §1), and now
  for $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$, with $`\psi_{\Omega_2}(\Omega_2\cdot 2)`$ the second such fixed point (NAME-OFFSET-G⁺, [VEBLEN.md](VEBLEN.md) §8).

## 4. The bottom of a chain of length 3

INC1-S is the statement "$`a \le_1 b`$ in $`R_2^S`$ implies $`a \le_1 b`$ in $`R_1^+`$". INC1-nonups is the same for $`R_2^C`$ and $`a`$ not a
$`\upsilon`$-point ([REACHES.md](REACHES.md) §4). $`U`$ is the class of $`\upsilon`$-points.

- **A gap in Lemma LEFT** (blocking point, found by this round's referee). The proof of LEFT in $`R_2^S`$
  ([REACHES.md](REACHES.md) §4) says that $`\Sigma_1`$-elementarity in the language of $`R_2^S`$ gives it for $`R_1^+`$. That is
  wrong: $`\le_1`$ of $`R_1^+`$ is defined through itself (Carlson 2001, p. 19; Wilken 2020, pp. 418, 420), so a $`\Sigma_1`$-copy in
  $`R_2^S`$ need not keep $`\le_1`$ of $`R_1^+`$. So LEFT, and the results that use it, now hold in $`R_2^S`$ only given INC1-S, as
  in $`R_2^C`$ only given INC1-nonups. Later both were reduced to Conjecture NOBAD, and now INC1-S and INC1-nonups are proved (Theorem INC1, 1 review,
  [BREAK.md](BREAK.md) §1). So LEFT, VEB and C3-VEB hold with no hypothesis.
- **Lemma PRINC-S** (proved, 1 review). In $`R_2^S`$, left ends of $`\lt_1`$ and right ends of $`\lt_2`$ are additively principal.
- **The ladder** (proved, 1 review; Lemma DIAG). $`C_0 = U'`$, $`C_{l+1}`$ is the diagonal of $`C_l`$, and $`C_l`$ is the
  intersection at limits $`l`$. $`C_1`$ is the class of fixed points of $`\iota \mapsto \upsilon_\iota`$, and $`C_2`$ that of $`\alpha \mapsto \Xi_\alpha`$.
- **Lemma VEB** (first proved given INC1-S in $`R_2^S`$, given INC1-nonups in $`R_2^C`$; 1 review; now unconditional, [BREAK.md](BREAK.md) §1; a minor fix
  to one case, from its review, is still to be written in). Let $`y \lt f_1 \lt \cdots \lt f_n`$ with
  $`y \lt_2 f_i`$ for all $`i`$, and $`s = f_n\cdot a_n + \cdots + f_1\cdot a_1 + y\cdot a_0 + b`$ with $`b \lt y`$ and $`a_i \lt \omega`$. If
  $`y \le_1 f_1 + s`$, then $`y \in (C_l)^{(b)}`$ with $`l = \omega^n\cdot a_n + \cdots + \omega\cdot a_1 + a_0`$. For example, $`y \lt_2 e`$ and
  $`y \le_1 e + y`$ give $`y = \upsilon_y`$.
- **Theorem C3-VEB** (same status). In every chain $`c_0 \lt_2 c_1 \lt_2 c_2`$: $`c_0 \in C_{\omega^\omega}`$, and $`c_0`$ is a limit point of
  $`C_{\omega^\omega}`$; every $`m \lt c_0`$ with $`m \le_1 c_0`$ lies in $`C_{\omega^\omega}`$, so $`m_3`$ is a $`\upsilon`$-point (no Conjecture MONO
  needed) with no $`\lt_1`$-predecessor; the $`\lt_2`$-successors $`d`$ of $`c_0`$ with $`d \le_1 c_1`$ are $`\upsilon`$-points. For the shape
  C3′′, $`C^*_3 = \{\upsilon_\Lambda, \upsilon_{\Lambda+\omega}, \upsilon_{\Lambda+\omega+1}\}`$: $`\Lambda = \upsilon_\Lambda`$ lies in $`(C_{\omega^\omega})'`$,
  $`\mathrm{lh}(c_1) = c_2`$, $`c_2`$ is the only $`\lt_2`$-successor of $`c_1`$, and $`c_0 \lt_2 \upsilon_{\Lambda+k}`$ for infinitely many $`k`$. But
  C3′′ is false ([BREAK.md](BREAK.md) §3), so these consequences of C3′′ are vacuous.
- **Not proved** (blocking point): "the least $`\Lambda`$ that the proved theorems allow is $`\Lambda_{struct}`$, the least limit point
  of $`C_{\omega^\omega}`$". It leaves out Theorem SKEL ([REACHES.md](REACHES.md) §3: $`c_0 \ge \nu_P`$ in $`R_2^S`$), which with C3-VEB gives
  $`m_3 \ge \rho_{\Lambda^*}`$ (the referee's argument). So the bound is: $`\Lambda`$ is at least the least element of $`(C_{\omega^\omega})'`$
  that is $`\ge \nu_P`$. By the conjectured names, $`\Lambda_{struct} \lt \Theta_P \le \Lambda^* \lt \nu_P`$ (order checked in Python and
  Lean), so $`\Lambda_{struct}`$ is excluded. These structural bounds still all lie below $`\theta_0`$. Now $`\Lambda_{struct} \lt \nu_P`$ and "no chain
  starts at $`\Lambda_{struct}`$" are proved without names or conditions ([BREAK.md](BREAK.md) §3, 1 review).
- **Certificates** ($`R_2^C`$; the author replayed all 39 runs, the referee replayed 7 again).
  $`\Lambda \gt m_3 \gt`$ the point of $`\Phi_3((0,0,0)(1,1,1)(2,2,2)(3,3,3))`$, which is above the point of $`\Phi_3(\mathrm{SRO})`$. If the
  conjecture of [README.md](README.md) §6 that the point of $`\Phi_3(\mathrm{SRO})`$ is $`\theta_0`$ holds, then $`m_3 \gt \theta_0`$. The
  stronger "$`\Lambda \ge \Lambda_{cert}`$" (the least limit point of $`C_{\omega^\omega}`$ above that point) needed INC1-nonups, which is now proved,
  so it holds ([BREAK.md](BREAK.md) §1).
- **Conjectures, now proved** ([BREAK.md](BREAK.md) §3, 1 review). $`\min C_l = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot l})`$ and
  $`\Lambda_{struct} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot\omega^\omega+1})`$. The lower half of CH ($`m_3 \gt \psi_{\Omega_1}(I_0)`$) is open; the
  route "upper half from C3′′" is gone, because C3′′ is false. The numeric C3′ needs
  $`\psi_{\Omega_1}(E + \theta)`$ to be a fixed point of $`\iota \mapsto \upsilon_\iota`$, which fails if Lemma REL is an equality there.

## 5. Checks

Each run was under 60 seconds; none is a proof.

- Pins: a search for coverings with raised parameters and a raised base $`\tau \in \{1, \varepsilon_0, \varepsilon_1\}`$ that send $`z`$ below itself,
  below $`\varepsilon_\omega`$ (where $`\le_1`$ of $`R_1^+`$ is given by Wilken's Thm 2.2). With the witness points of the reach paper:
  0 counterexamples in 70 finished searches (50 hit the time limit). Closing only under components, partial sums
  and $`\mathrm{lh}`$ is not enough (57 of 120 fail); RC-PIN does not use that closure.
- Reaches: the program `phi3def2` on 11 standard matrices gives the reaches $`\delta + \varepsilon_{\rho+\omega}`$, $`\delta + \sigma`$, $`\delta + \sigma + 1`$,
  $`\delta + \sigma + \rho`$ and $`\delta + \omega^{\sigma+1}`$; the referee's 2 new matrices give $`\delta + \sigma\cdot 2`$ and $`\delta + \sigma + c`$ with
  $`c \in \mathrm{seg}(\rho)`$, as EXACT-A predicts (the matrices are matched to indices by analogy).
- Names: the hull condition against the normal-form test on 4,004 arguments, 0 mismatches. 300 random $`\eta`$ for each of 3
  seeds, many of them $`\ge \theta`$: "normal form iff every countable piece is below $`H(\eta)`$", 0 mismatches; $`H`$ strictly
  increasing on about 55,000 pairs; DOWN on 3,325 instances. 22 and 23 named terms are normal forms and increasing, in
  Python and in Lean (test files, not proofs). 4 matrices above $`\Lambda_\Gamma`$ give the reaches that NAME-OFFSET predicts
  (evidence only).

## 6. Open

- The exact reaches above $`\Theta_A`$: H-RC for the later segments ($`\mathrm{seg}(\sigma)`$ above $`\varepsilon_{\sigma+\omega}`$, $`\mathrm{seg}(\upsilon_{\lambda+n})`$,
  $`\mathrm{seg}(\tau_1)`$, the later blocks); the general pin over several segments (reduced to CL-FIN, LHPAR\* and part of the
  finite-set test T1); points $`y \ge \delta_j\cdot\omega`$; $`R_2^C`$ above $`\rho_{\Theta_A+\omega^2}`$. Above any base below $`T_\omega`$ the reaches follow the
  formal-reach recursion run above that base (TAIL-GAP, now proved, 1 review, [COVER.md](COVER.md) §5.1). Below $`\nu`$ its value at every
  restart index that is not Γ-type has the closed form of OFF-V (proved for $`\gamma = 0`$, and now for $`\gamma \ge 1`$ too; [FANFREE.md](FANFREE.md) §3, §7.3); what is open is
  the reaches at limits of critical indices ([FANFREE.md](FANFREE.md) §7.3); now the closed form reaches offset $`\rho^\rho`$, and what is open is the reaches at
  limits of fixed points of the enumeration of the Klammer-critical class ([FANFREE.md](FANFREE.md) §10.3).
- CL-FIN and LHPAR\*, and so the elementary recursive assignments. Now CL-FIN and the Cl\*-form of LHPAR\* are proved; the
  sharp form of LHPAR\* fails as stated, and "elementary recursive" is an outline ([BREAK.md](BREAK.md) §4).
- The closed form of $`c^+`$ on $`[\Lambda_\varepsilon, \Theta_1)`$; the names of $`\Theta_P`$, $`\Theta_1`$, $`\Theta_A`$, $`\Lambda^*`$ and $`\nu_P`$; how far $`D`$
  reaches; the names half of the claim above $`\Lambda_\varepsilon`$. Now the closed form holds for offsets up to $`\varepsilon_{\zeta_{\rho+1}+1}`$, $`\Theta_P`$ is named, and the
  claim holds up to $`\rho_{\Lambda'+\omega^2}`$ ([FANFREE.md](FANFREE.md) §10.4); left: the closed form on $`(\Lambda', \Theta_1)`$ and the other names. Now the closed form
  holds for every restart with $`e_\lambda \le \psi_{\Omega_2}(\Omega_2) + 1`$ and the claim up to $`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$; $`\Theta_1 = H(\theta)`$ is reduced to an open hull lemma ([VEBLEN.md](VEBLEN.md) §1). Now the closed form holds for
  $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$ and the claim up to $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$; the names of $`\Theta_1`$ and $`\Theta_A`$ need only the open lemma PAR-SAME ([VEBLEN.md](VEBLEN.md) §8). Now PAR-SAME is proved, $`\Theta_1`$ and $`\Theta_A`$
  are named, and the claim holds up to $`\psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$; for $`\Lambda^*`$ and $`\nu_P`$ only lower bounds are proved ([THETA.md](THETA.md) §1). Now $`\Lambda^*`$ and $`\nu_P`$ are named and the claim holds up to
  $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$ ([THETA.md](THETA.md) §9.1), then up to $`X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2)`$ with $`G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})`$ ([SHIFT.md](SHIFT.md) §1), and, given FRAG, up to $`X_5`$ ([SHIFT.md](SHIFT.md) §8.1) and then up to $`X_8`$ ([SHIFT.md](SHIFT.md) §9.1) and $`X_9`$ ([SHIFT2.md](SHIFT2.md) §1.1) and $`X_{11}`$ (§2.1 there) and $`X_{12}`$ (§3.1 there) and $`X_{13}`$ ([SHIFT3.md](SHIFT3.md) §1.1) and $`X_{14}`$ (§2.1 there) and $`X_{15}`$ ([SHIFT4.md](SHIFT4.md) §1.1) and $`X_{16}`$ (§1.4 there) and $`X_{17}`$, $`X_{18}`$ (§2.1, §2.2 there) and $`X_{19}`$ ([SHIFT5.md](SHIFT5.md) §1.1) and $`X_{21}`$ (§2.1 there) and $`X_{22}`$, $`X_{23}`$ ([SHIFT6.md](SHIFT6.md) §1.1, §2.1, with the repair of §3.1 there) and $`L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P')`$ ([SHIFT7.md](SHIFT7.md) §1.1), which is $`\nu_C`$ given FRAG (§2.1 there), and above it up to $`X_A = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P' + \omega^{\theta+3}\cdot 2)`$ (§3.2 there), then up to $`L(\omega^2)`$ and $`L(\Omega_1\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1+1})`$ ([SHIFT8.md](SHIFT8.md) §1.1, §1.2), then up to $`L(\varepsilon_{\Phi_\Omega+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\varepsilon_{\Phi_\Omega+1}})`$ (§2.1 there).
- INC1-S and INC1-nonups are now proved ([BREAK.md](BREAK.md) §1); RIGHT (every $`\lt_2`$-right end is a $`\upsilon`$-point) is now proved in $`R_2^S`$ ([COVER.md](COVER.md) §5.1), and open in $`R_2^C`$ above $`\beta_0`$.
- $`C^*_3`$: the least bottom (above $`\nu_P`$), the upper half, the lower half, and Conjecture CH ([BREAK.md](BREAK.md) §10); the first fan is above $`T_\omega`$, and it needs an inaccessible given the open hypothesis
  $`FF_N`$ ([BREAK.md](BREAK.md) §7.4; now equivalent to $`m_F \ge \theta_0`$, [FANFREE.md](FANFREE.md) §4), or given the weaker open hypothesis that $`\min\{m : m \le_1 x_F\}`$ is $`\ge \theta_0`$ (now equivalent to a lower bound for
  fan-free patterns whose right ends have no reach, [COVER.md](COVER.md) §5.3; several uniform steps of it are proved, [COVER.md](COVER.md) §6.1, and
  $`m_F \gt \nu_C`$, [COVER.md](COVER.md) §6.4); in $`R_2^C`$ the bottoms of chains are
  characterized, and $`c_0 \gt m_3 \ge \sup_n \varphi_n \gt f_0 \gt x_F`$, with $`\varphi_n`$ the least apex of a closed $`n`$-fan ([COVER.md](COVER.md) §1–2).
