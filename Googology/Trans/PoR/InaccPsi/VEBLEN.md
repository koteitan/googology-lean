[← Back](README.md) | [English](VEBLEN.md) | [Japanese](VEBLEN-ja.md)

# $`R_2^+`$, the eleventh and twelfth rounds: offsets past Γ, native codes up to $`\Phi_1`$, symbols for the shapes of $`\Phi_3`$, and a direct $`\Sigma_2`$ argument

This page continues [FANFREE.md](FANFREE.md), and [THETA.md](THETA.md) continues it. The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from 2026-10; they come from
the eleventh round (§1–§7) and the twelfth round (§8–§14), four papers each. A statement with a blocking point against it is listed under **Not proved**; a statement that its
referee found to restate the target, or to be trivial, is listed under **Not counted**. A certificate counts only when it was replayed.
None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009,
p. 97, announces. No result on this page is in Lean, and no Lean file was added. The notation is that of [FANFREE.md](FANFREE.md).

Every paper was refereed once, so a result here has 1 review unless a count is given. In each round one paper (§1, §8) checked a Lean test
file of named points with leanman (green, and green again in the referee's rerun); these files only compare terms (`#eval`, no theorem), and they are
not added to the library. The other papers make no Lean claim. The papers number the levels one lower; here they are renumbered (a point of
$`U_2`$ below is a point of their first level).

## 1. Offsets past Γ, and the claim up to $`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$

Notation of [FANFREE.md](FANFREE.md) §10.4. A strongly critical ordinal is a value of $`\Gamma`$, and $`\Gamma_a`$ is the $`a`$-th one. $`X`$ is Γ-fixed if $`\Gamma_X = X`$, and
$`\Gamma^{\mathrm{fp}}(x)`$ is the least Γ-fixed ordinal above $`x`$. $`\bar\varphi_\delta`$ lists in order the values of $`\varphi_\delta`$ that are not fixed points of
$`\varphi_\delta`$. $`\vartheta^\tau`$ is Wilken's collapse over the base $`\tau`$ (Wilken 2007, APAL 145, 130–161). For a term $`t`$, $`t[\Omega_1 := r]`$ puts $`r`$ for
$`\Omega_1`$, $`\Gamma_{a[\Omega_1 := r]}`$ for $`\Gamma_a`$ and $`\Gamma^{\mathrm{fp}}(r)`$ for $`\psi_{\Omega_2}(\Omega_2)`$.

- **Repairs of [FANFREE.md](FANFREE.md) §10.4** (proved). ATTAIN-NAMES holds with the added hypothesis $`\omega^{1+t} \in D`$ (for example, every constant of $`t`$ below
  $`\upsilon_1`$); $`\Theta_1 \gt \Lambda' + \omega^2`$, so $`\rho_{\Theta_1} \gt \rho_{\Lambda'+\omega^2}`$; in NAME-LAYERS, $`e`$ gives the canonical form only up to the rest's logend;
  and the referee's remark of [FANFREE.md](FANFREE.md) §10.4 is now proved: the claim held on $`[0, H(\varepsilon_{\zeta_{\Omega_1+1}+1}\cdot\omega + \omega^2))`$.
- **VEB-THETA** (proved, from Wilken 2007, L.3.5, 3.7, 3.30, 4.3, 4.4). Let $`\tau`$ be 1 or a $`\upsilon`$-point below $`\upsilon^*`$. For
  $`1 \le \delta \lt \tau^\infty`$ and $`\eta \lt \tau^\infty`$: $`\vartheta^\tau(\Omega_1\cdot\delta + \eta) = \bar\varphi_\delta(o_\delta + \eta)`$, where $`o_\delta = \tau`$ if $`\delta \lt \tau`$, $`o_\delta = 1`$ if $`\delta \ge \tau`$ is
  strongly critical, and $`o_\delta = 0`$ otherwise. So the level $`\Omega_1\cdot\delta`$ of Wilken's system is the $`\delta`$-th Veblen function made
  fixed-point free, and the strongly critical ordinals are exactly the values of level $`\ge \Omega_1^2`$. EPS-THETA of [FANFREE.md](FANFREE.md) §10.4 is the case $`\delta = 1`$.
  (The referee: one inequality in the proof of the lemma FIXP is false when $`\delta`$ is strongly critical; the fact that is needed holds.)
- **GC and GAM-THETA** (proved). Every $`\upsilon`$-point is Γ-fixed. $`\Gamma^{\mathrm{fp}}(\tau) = \vartheta^\tau(\Omega_1^2 + \Omega_1)`$, and $`\vartheta^\tau(\Omega_1^2 + \eta) = \Gamma_{\tau+1+\eta}`$
  while this is below $`\Gamma^{\mathrm{fp}}(\tau)`$.
- **EXACT-G** (proved). For $`\upsilon`$-points $`s \lt r`$, Wilken's base change from $`r`$ to $`s`$ is exact on every term built from constants
  below $`s`$, the base, $`+`$, $`\varphi`$ and $`a \mapsto \Gamma_a`$ below $`\Gamma^{\mathrm{fp}}`$ of the base, and on $`\Gamma^{\mathrm{fp}}`$ of the base plus 0 or 1 (before:
  EXACT-Z, with $`\varepsilon`$ below $`\varepsilon_{\zeta^x+1}`$).
- **PSI2 and the InaccPsi side** (proved). $`\psi_{\Omega_2}(\beta) = \Gamma_{\Omega_1+1+\beta}`$ for $`\beta \lt \psi_{\Omega_2}(\Omega_2)`$, and
  $`\psi_{\Omega_2}(\Omega_2) = \Gamma^{\mathrm{fp}}(\Omega_1)`$. The Veblen components and the Γ-indices of hull elements stay in the hull (COMP-V,
  COMP-G); normal forms of these terms compare in the same way at every Γ-fixed strongly critical base (UNIF-G); TERM-G and the hull
  closure. (The referee: the induction measure of UNIF-G must be changed: first decide normal forms, then compare; the statement is right.)
- **Theorem NAME-OFFSET-G** (proved). For every restart index $`\lambda`$ with $`\rho_\lambda \lt \upsilon^*`$ and $`e_\lambda \le \psi_{\Omega_2}(\Omega_2) + 1`$:
  $`c^+(\lambda) = (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$. This contains NAME-OFFSET-Z of [FANFREE.md](FANFREE.md) §10.4.
- **The landmarks** (proved). The least restart with $`c^+ = \Gamma_{\rho+1}`$ is $`H(\Gamma_{\Omega_1+1}) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(0)})`$;
  with $`c^+ = \Gamma_{\rho\cdot 2}`$ it is $`H(\psi_{\Omega_2}(\Omega_1))`$; with $`c^+ = \Gamma^{\mathrm{fp}}(\rho)`$ it is $`H(\psi_{\Omega_2}(\Omega_2))`$; with
  $`c^+ = \Gamma^{\mathrm{fp}}(\rho) + 1`$ it is $`\Lambda_{\mathrm{fp}} = H(\psi_{\Omega_2}(\Omega_2)\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2)+1})`$. So
  $`\Lambda_{\mathrm{fp}}`$ is to $`\Gamma^{\mathrm{fp}}`$ what $`\Lambda_\varepsilon`$ is to $`\alpha \mapsto \varepsilon_{\alpha+1}`$. And $`\Theta_1 \gt \Lambda_{\mathrm{fp}} + \omega^2`$. (The referee: the place cited for
  $`\omega^{\psi_{\Omega_2}(\Omega_2)+1} \in D`$ does not cover it; a one-line repair gives it.)
- **STRUCT″** (proved). STRUCT′ of [FANFREE.md](FANFREE.md) §10.4 holds on $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$, in $`R_2^C`$ and $`R_2^S`$, with every restart reach in closed form
  by NAME-OFFSET-G. (The referee: that the two structures agree there is EQB-A, which needs Lemma FRAG; FRAG is proved.)
- **Wilken's claim on $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$ in $`R_2^C`$**, both halves (proved): every ordinal below
  $`\rho_{\Lambda_{\mathrm{fp}}+\omega^2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2)+1} + \omega^{\theta+2})`$ is in the core and is the value of an InaccPsi normal
  form with collapse arguments below $`I_\omega`$. Before: $`[0, \rho_{\Lambda'+\omega^2})`$. As in [FANFREE.md](FANFREE.md) §10.4, the new fact for the claim is the position
  $`\Lambda_{\mathrm{fp}} + \omega^2 \lt \Theta_1`$. **Remark** (the referee's, not counted): the same proof reaches the offsets $`\psi_{\Omega_2}(\Omega_2) + c`$ with $`c \lt \omega`$,
  and probably every offset below $`\Gamma_{\Gamma^{\mathrm{fp}}(x)+1}`$.
- **Theorem KV-NAMES** (proved, given Theorem KV of [FANFREE.md](FANFREE.md) §10.3 with its repairs). For every restart index $`\lambda`$ with
  $`\rho_\lambda \lt \min(\nu_C, \upsilon^*)`$ and $`e = e_\lambda`$: if $`\lambda \notin \mathrm{Fix}_1`$, then $`e = \mathrm{logend}(\lambda)`$; if $`\lambda \in \mathrm{Fix}_1 \setminus K`$ has canonical
  form $`(A, \eta)`$, then $`e = P_A(\Omega_1) + \mathrm{logend}(\eta)`$; $`\lambda \in K`$ iff $`e \ge \Omega_1^{\Omega_1}`$; and $`\lambda \in F_B`$ iff $`e \ge P_B(\Omega_1)`$, for every
  symbol $`B \ne 0`$ with entries below $`\lambda`$. So the Klammer reaches of KV are InaccPsi names:
  $`\mathrm{lh}(\rho_\lambda) = H(\eta_\lambda + \omega + 1) + P_A(\rho) + \mathrm{logend}(\eta)`$. On this range this proves the conjecture that the Klammer form of $`\iota(\eta)`$
  is the base-$`\Omega_1`$ expansion of $`\mathrm{logend}(\eta)`$; NAME-LAYERS is the case of positions $`\le 3`$. The first point of $`K`$ is $`H(\omega^{\Omega_1^{\Omega_1}})`$.
  Whether $`\nu_C \lt \upsilon^*`$ is open.
- **$`\Theta_1`$** (proved as a reduction). Let $`T^{\Omega_1}`$ be Wilken's system over the base $`\Omega_1`$. **H3** (the shifted STEP-0, proved):
  $`T^{\Omega_1} \cap \Omega_2 \le \theta`$. **THETA1-RED** (proved as implications): (H2b) gives $`\Theta_1 \le \iota(\theta)`$; (H2a) gives $`\Theta_1 \ge \iota(\theta)`$ and
  the claim on $`[0, H(\theta))`$; both together give $`\Theta_1 = H(\theta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$. (H2a) and (H2b) together say that
  the InaccPsi hull of $`(\Omega_\omega + \theta\cdot g, H(g))`$ and Wilken's hull $`T^{\Omega_1}[H(g)]`$ have the same elements below $`\theta`$.
- **Not proved**: $`\Theta_1 = H(\theta)`$ and the claim on $`[0, H(\theta))`$: (H2a) and (H2b) are open beyond $`\psi_{\Omega_2}(\Omega_2)`$, as the paper says.
  The paper's sentence "(H2a) and (H2b) hold on $`[0, \psi_{\Omega_2}(\Omega_2)]`$" is not proved either (one direction of (H2b) and the shifted
  VEB-THETA are only asserted); no proved result uses it. (The twelfth round reduces $`\Theta_1 = H(\theta)`$ to another lemma, PAR-SAME, §8.)
- **Points of $`U_2`$ and long restarts** (proved). Every point of $`U_2`$ below $`\upsilon^*`$ and every long restart below $`\min(\nu_C, \upsilon^*)`$ is $`H(\eta)`$
  with $`\mathrm{logend}(\eta) \gt \psi_{\Omega_2}(\Omega_2) + 1`$ (and $`\ge \theta`$ given (H2a)).
- **Open**: an InaccPsi upper bound for $`\nu_C`$. It needs a positive relation, a $`\lt_2`$-pair that contains a second pair, at a named point
  in zone C, above $`\Theta_1`$, where no reach is known.

## 2. Native codes up to $`\upsilon_1`$, and one level of references

Notation of [FANFREE.md](FANFREE.md) §10.2. For an $`\varepsilon`$-number $`x = \vartheta(D_x + \eta_x)`$ ($`D_x`$ a multiple of $`\Omega_1`$, $`\eta_x \lt \Omega_1`$),
$`x^+ = \vartheta(D_x + \eta_x + 1)`$, and $`\iota_x`$ is Wilken's level shift (APAL 145, 130–161, Def 7.1).

- **SHIFT** (cited; the referee checked the places and their hypotheses). The level shift that [FANFREE.md](FANFREE.md) §10.2 left open is in Wilken's paper:
  Def 7.1, Lemma 7.2, Cor 7.3, Lemmas 7.4, 7.8, 7.9. **Lemma SUBST** (proved): for $`\varepsilon`$-numbers $`g \lt h`$, the zone translation
  $`\sigma_{g\to h}`$ is the substitution $`g := h`$ in Wilken's terms, and it commutes with $`\iota`$, with $`x \mapsto x^+`$ and with localization. (The
  referee: one place cited for $`\omega^z`$ is the wrong lemma, but the claim holds by Lemma 4.2 and SUBST (b); and SUBST (c) is used at $`x = g`$,
  a case that holds by Lemma 5.5 and should be added.)
- **The reach** (definition). $`\rho(x)`$ is Wilken's true $`R_1^+`$ reach (Wilken, APAL 145, 162–175, Def 4.1, which is the fold of
  [PSS/POR.md](../../BMS/PoR/PSS/POR.md) §3.3), with its last part replaced by the full code $`\Lambda_x = \iota_x(D_x)\cdot 2 + \eta_x`$, added after the fold.
  Wilken's own reach is not monotone in the needed sense: for $`g = \varepsilon_\omega`$, $`h = \varepsilon_{\omega+1}`$, $`\sigma(\mathrm{lh}(g)) = h\cdot 2 + 1 \gt \mathrm{lh}(h) = h\cdot 2`$.
- **Lemmas R+, LOC, LAM, UNIF, MON** (proved). $`\rho(x) \lt x^+`$; the reach intervals are nested or disjoint for all ordinals below $`\upsilon_1`$;
  $`\rho`$ commutes with $`\sigma`$; and $`g \lt h`$ with $`a_g \lt a_h`$ gives $`\sigma_{g\to h}(\rho(g)) \lt \rho(h)`$. So the case EQUAL-TOP of [FANFREE.md](FANFREE.md) §10.2 does not arise. (The
  referee: the hardest case of MON really occurs, for example at $`g = \vartheta_0(\vartheta_1(\vartheta_2(\Omega_3)))`$.)
- **FIN, PAT-U, HOST-U, GROUP, CODE-U** (proved). The codes are finite RF fan-free, L1p-free patterns. A new $`\varepsilon`$-number index is placed with
  its zone, the zone points recursively with theirs, and each group is reflected by R1 at its host.
- **Theorem IDX-U** (proved). $`N(\alpha') \ll N(\alpha)`$ for $`\omega \le \alpha' \lt \alpha \lt \upsilon_1`$. With HOST2 ([FANFREE.md](FANFREE.md) §7.2): $`\iota(\mathrm{CH}_2) \ge \upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$
  (before: $`B`$).
- **Theorem IDX-REF** (proved; one step, STEP-IN, is written only as a sketch, the paper's §5 "relativized" in 8 lines with three new cases not written out;
  the referee checked the three cases by hand and they hold, but the relativized placement was never run). The index family $`[\omega, \upsilon_1)`$
  followed by one copy of $`[\upsilon_1, \upsilon_2)`$ for each $`\beta \lt \upsilon_1`$ (read with the base $`\psi_{\Omega_1}(\Omega_\beta)`$) has order type $`\upsilon_2\cdot\upsilon_1`$,
  and its codes are $`\ll`$-increasing (Lemma REF of [FANFREE.md](FANFREE.md) §7.2 at limits, and new Lemmas UNIV-P and BRIDGE). So $`\iota(\mathrm{CH}_2) \ge \upsilon_2\cdot\upsilon_1`$.
  (STEP-IN is now written in full and refereed, §9.)
- **Not counted**: the paper's remark that the inflated reach is necessary. The failures of Wilken's reach show only that this placement
  plan breaks with it.
- **Not proved**: $`\iota(\mathrm{CH}_2) \ge \theta_0`$, as the paper says. The gap: nested references, which stay below $`\psi_{\Omega_1}(\Omega_{\Omega_1}) \lt \theta_0`$, and
  then the block grammar of the $`\Omega`$-levels.

## 3. The shapes of $`\Phi_3`$: a periodic symbol for the steps with $`t = 1`$

Notation of [FANFREE.md](FANFREE.md) §7.1 and [FANFREE.md](FANFREE.md) §10.1. $`P_m`$ is the subtree of the bad root $`R`$ in $`A[m]`$, and $`H`$ is the subtree of $`R`$ in $`A[1]`$ with a hole, so that
$`P_m = H[P_{m-1}]`$. The theorems are about the text definition of $`\Phi_3`$, and everything is in $`R_2^C`$.

- **Lemma SEQ** (proved). A procedure compares column words made of plain columns and of "segments", whose length grows linearly in $`j`$.
  It returns the order that holds for every $`j \ge J_0`$, or it reports that there is none. (The referee: one branch of its jump rule can never run.)
- **Lemma SYM-P** (proved as a paper argument about the program's Python semantics, like Lemma SYM of [FANFREE.md](FANFREE.md) §10.1). A symbol $`Z`$ stands for
  $`P_j`$ for all $`j \ge J_0`$ at once; its children are unfolded lazily and exactly by $`P_m = H[P_{m-1}]`$. If the program's run on $`Z`$ finishes, it gives
  $`\Phi_3`$ for every $`j \ge J_0`$. This removes the obstruction of ROOT with $`t = 1`$ in [FANFREE.md](FANFREE.md) §10.1. (The referee: the proof misses three of the program's
  identity tests, and it uses without proof that the run does not depend on how terms are stored or on the order of calls; this is
  checked only, with 0 differences when all 3,166 sample matrices are built in three ways.)
- **Theorem PER** (proved, given SYM-P). For 292 of the 302 ROOT matrices with $`t = 1`$: the shape of $`\Phi_3(A[n])`$ for every $`n`$, with step 1
  or 2 and a fixed high part.
- **Theorem SELF-CHAIN-C** (proved; the referee corrects an index in one formula to $`\beta(P_{n-s})`$). FS$`^+`$ for every $`n`$ on 285 of them,
  among them the 58 that [FANFREE.md](FANFREE.md) §10.1 had only given a condition checked for small $`n`$.
- **Theorems IX-PER, IX-CORE, SUM-CORE** (proved). For classes I and III with $`t = 1`$: an index that is a pair term (127 new matrices) and a core
  at $`R`$ (94 new); for SUM, 62 new. (The referee: the symbolic check of IX-PER proves only that the index part is contained in the claimed set,
  not equal to it; FS$`^+`$ needs only this inclusion, and equality is checked for $`n \le 9`$.)
- **The proved classes on the sample** of [FANFREE.md](FANFREE.md) §1 (3,166 matrices):

| class | matrices | proved for every $`n`$ | given LOW | given a condition checked for small $`n`$ | open |
|---|---|---|---|---|---|
| I | 581 | 277 | 21 | 0 | 283 |
| SUM | 603 | 480 | 0 | 7 | 116 |
| ROOT | 635 | 491 | 0 | 0 | 144 |
| III | 1,347 | 194 | 0 | 0 | 1,153 |
| all | 3,166 | 1,442 (before: 874) | 21 | 7 | 1,696 |

- Of the 267 matrices that the list of [FANFREE.md](FANFREE.md) §10.1 left out, 37 are now proved (all of class III with $`t = 1`$ and a trio subterm).
- **Open**: UNIF-FS below SRO. The 1,724 matrices that are not proved fall into these classes (the referee checked that the counts add up):

| class | matrices | why it is open |
|---|---|---|
| $`t = 0`$, bad root not a root column | 882 | the copies are siblings: a repeated run of children, not a periodic subterm |
| $`t = 2`$ | 460 | chains that get deeper with $`n`$; a new theorem is needed |
| $`t = 1`$, bad root in the $`\Omega`$-level structure (III) | 201 | the run goes down into $`Z`$; it needs symbols for images (outline only) |
| other $`t = 1`$ of classes I and III | 140 | the run goes down into $`Z`$, there is no map at $`n = 0`$, or a core node lies above the template |
| ROOT, $`t = 1`$ | 17 | 7 meet the base obstruction of [FANFREE.md](FANFREE.md) §7.1 (a node of the base block reaches into the first block); 10 fail PER |
| SUM, $`t = 1`$ | 24 | 13 where the changed summand interleaves with the fixed ones, 11 with a core of class III |

## 4. $`\nu_C = \nu_S`$ by a direct $`\Sigma_2`$ argument

Notation of [COVER.md](COVER.md) §6.3 and [FANFREE.md](FANFREE.md) §10.3: $`x = x_2`$, $`\nu = \nu_C`$, $`U_2`$, $`S_n`$, $`S_\omega`$, and $`R`$, the structure that $`R_2^C`$ and $`R_2^S`$ share below
$`\nu_C`$. A copy of a finite set is **exact** if the increasing bijection keeps $`0, +, \le, \le_1, \le_2`$ in both directions (an isomorphism), not only
forward (a covering).

- **ET** (proved, but not new: the referee finds that it is Theorem T2 of [README.md](README.md) §3, which is already an "iff"; not counted).
  $`x \le_2^S \nu`$ iff for all finite $`p \subset x`$, $`Y \subset S_\omega`$ and $`k`$ there is $`\tilde Y \subset x`$ with the same diagram over $`p`$, such that every
  $`k`$-point extension of $`\tilde Y`$ in $`R|x`$ is realized over $`Y`$ in $`R|\nu`$. The long-restart obstruction NEED-C of [FANFREE.md](FANFREE.md) §10.3 applies to it from $`k = 5`$
  (ET-LONG, proved).
- **HULL** (proved). $`x \le_2^S \nu`$ if for all finite $`p`$ and $`Y`$ there are a $`\Sigma_1`$-elementary substructure $`M`$ of $`R|x`$ and an embedding
  $`j : M \to R`$ that fixes $`p`$ and has $`Y \subseteq j[M]`$. So LBC gives $`\Sigma_2`$ directly, without Wilken 2020, Prop 21.11. (The referee: the remark that
  a global LBC map has this property is not checked.)
- **DOWN-EX and UP-EX** (proved; the citations of Carlson 2009, Defs 9.4, 10.1, 13.10 and Thms 14.10, 14.11 match their hypotheses). Over every
  isominimal set of $`R_2^C`$ that contains $`x`$ and $`\nu`$, Carlson's two 2-reflection rules give exact copies, not only coverings: below $`x`$
  (downward), and just below $`\nu`$ above the rest of the set (upward). This corrects a remark of the seventh-round paper of [COVER.md](COVER.md) §6.3 that they
  give "only coverings".
- **L17-EX** (part (2) proved; part (1) not proved as stated). (2): for $`Y \subset S_\omega`$, cofinally below $`x`$ there are exact copies $`\tilde Y`$ of $`Y`$
  over a given $`X \subset x`$, with $`\tilde y \le_1 x`$ iff $`y \le_1 \nu`$. (1), "every pattern over $`X`$ realized cofinally below $`x`$ is realized cofinally
  below $`\nu`$", needs the copies to be closed, which an isomorphism does not give (the referee's example: $`X = \emptyset`$, $`Z = \{\omega\}`$,
  $`Z' = \{\omega+1\}`$); with that hypothesis added it holds, and that is enough where it is used. These are the exact forms, at $`(x, \nu)`$, of
  Wilken 2021, Lemma 1.7, whose covering forms were known.
- **TOP** (proved; the referee checked every kind of relation). Take $`\tilde Y`$ to be the downward copy of $`Y`$. Every extension of $`p \cup \tilde Y`$
  in $`R|x`$ that lies above $`\tilde Y`$ and contains no sum $`z + \tilde y`$ with $`\tilde y \in \tilde Y`$ is realized over $`p \cup Y`$ in $`R|\nu`$, with the same diagram.
  This covers the pattern of NEED-C: the upward rule gives its long restart in $`S_\omega`$ exactly, with no reach value. (The referee: "every
  long-restart pattern above the copy" holds only for such extensions.)
- **DECOUPLE** (proved). A point below the copy $`\tilde x = \upsilon^2_m`$ of $`x`$ relates to $`\tilde Y`$ by $`\le`$, $`\le_1`$, $`\le_2`$ exactly as it relates to $`Y`$
  (Lemma CUT); a point between $`\tilde x`$ and $`\max\tilde Y`$ has no $`\le_1`$- or $`\le_2`$-relation to a point above the copy.
- **Not proved** (blocking point): "(LOC) and (TR) give $`\nu_C = \nu_S`$". Here (LOC) is a local base change for the finite hull $`[\tilde x, \max\tilde Y]`$,
  and (TR) handles the sums $`z + v`$ with $`z`$ above the copy and $`v`$ in the hull. The criterion fixes $`\tilde Y`$ before the extension, so the extension
  may contain a point $`t \lt \tilde x`$ outside the isominimal set, and then sums such as $`z + t`$ fall under none of the tools (example:
  $`\{t, z, z + t\}`$, where $`z \le_1 z + t`$ must carry over). The correct residue is (LOC) and (TR) with an arbitrary finite set $`T \lt \tilde x`$ held
  fixed. So the reading of GHOST-SHAPE, "a ghost uses (LOC) or (TR)", is not proved either; its literal statement is proved but trivial
  (not counted).
- **Open**: $`\nu_C = \nu_S`$. The paper found no explicit $`\Sigma_2`$ sentence that separates $`R|x`$ from $`R|\nu`$.

## 5. Status after the eleventh round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$, with the reaches there in closed form (§1); on the range of
  GEN below $`\nu_C`$ the Klammer forms of the restarts are read off their names (KV-NAMES); $`\Theta_1 = H(\theta)`$ is reduced to the hull
  agreement (H2a) and (H2b).
- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 1,442 of the 3,166 sample matrices (§3); the
  native codes are ordered on $`[\omega, \upsilon_1)`$ and on one level of references, so $`\iota(\mathrm{CH}_2) \ge \upsilon_2\cdot\upsilon_1`$ (§2).
- The first inaccessible: $`H_m`$ is open; it would follow from $`\iota(\mathrm{CH}_2) \ge \theta_0`$.
- Upper bounds: no InaccPsi bound is proved for any $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: over isominimal sets the 2-reflection copies are exact, and every extension above the copy is matched (TOP); what is
  left is (LOC) and (TR) with a fixed finite set below the copy.

## 6. Checks of the eleventh round

Each run was under 60 seconds; none is a proof. Certificates count only when replayed.

- Names (§1). The 25 named points are normal forms and strictly increasing, in Python and in a Lean test file (green; the referee's
  rerun is byte-identical and green). $`\psi_{\Omega_2}`$ behaves as PSI2 says on samples. UNIF-G at the bases $`\Omega_1`$, $`\Omega_2`$, $`\Omega_3`$: 48,180
  comparisons, 0 mismatches (the referee: only at cardinal bases, while NAME-OFFSET-G uses it at countable $`\upsilon`$-points; the proof covers
  that case, the check does not). 197 offsets below $`\psi_{\Omega_2}(\Omega_2)`$: 38,612 ordered pairs, 0 mismatches. The referee's own probe of
  PSI2 (among others 33,436 $`\varphi`$-terms): no counterexample. VEB-THETA and EXACT-G are about Wilken's system, which has no implementation
  here, so they were not tested.
- Codes (§2). Placement in realized order: 21,125 steps, 20,159 of them past $`B`$, zones nested to depth 3; MON and UNIF on 6,968 pairs, LAM
  on 16,846, 20,712 codes; every altered rule is caught (no fold; Wilken's reach, which fails at 1,730 of 6,299 steps; a second host). 12
  certificates in the predicted direction, all replayed; none in 2 reverse searches. One run hit the time limit and is not counted. The
  referee: MON on 7,180 + 831 + 12,185 pairs, UNIF on 81,965 points, LAM on 92,306 and LOC on 197,192 tests, placement with new seeds (2,629
  steps): 0 failures. (The referee: the paper describes which run was killed in two different ways, and one development run has no output
  file.)
- Shapes (§3). The symbolic templates equal the concrete $`\Phi_3`$ for 4 values of $`j`$ on every accepted matrix (285 ROOT, 249 IX-PER, 245
  IX-CORE); 603 accepted random matrices beyond the sample are all valid. The referee: SEQ on 60,000 word pairs (53,171 decided, 10,616 of them by
  a jump), 0 wrong; PER and SELF-CHAIN-C at higher levels ($`n`$ up to 11 for step 1 and up to 14 for step 2); IX-PER and IX-CORE up to $`n = 9`$; all
  3,166 matrices built in three ways, 0 differences. (The referee: for IX-PER the validation compares only the nodes from the template up, so it
  covers the templates, not the index part.)
- $`\Sigma_2`$ (§4). The paper ran nothing. The referee checked one fact on sums used in TOP on 93,411 random cases below $`\omega^\omega`$, 0 failures.

## 7. Open after the eleventh round

The twelfth round changed this list; the current list is §14.

## 8. Offsets up to the second Γ-fixed point, and $`\Theta_1`$ reduced to one lemma on parameters

Notation of §1. $`\Gamma^{\mathrm{fp}}_2(x)`$ is the least Γ-fixed ordinal above $`\Gamma^{\mathrm{fp}}(x)`$. Put $`b_\Gamma(z) = z + 1`$ if $`z = F + n`$ with $`F`$ Γ-fixed and $`n \lt \omega`$, and
$`b_\Gamma(z) = z`$ otherwise; so $`a \mapsto \Gamma_{b_\Gamma(a)}`$ lists the strongly critical ordinals that are not Γ-fixed. $`C_g`$ is the InaccPsi hull of
$`(\Omega_\omega + \theta\cdot g, H(g))`$, and $`T^{\Omega_1}`$ is Wilken's system over the base $`\Omega_1`$ (§1). In $`t[\Omega_1 := r]`$ also $`\psi_{\Omega_2}(\Omega_2\cdot 2)`$ goes to $`\Gamma^{\mathrm{fp}}_2(r)`$.
$`\Lambda_{\mathrm{fp}2} = H(\psi_{\Omega_2}(\Omega_2\cdot 2)\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2\cdot 2)+1})`$.

- **Repairs of §1** (proved). The three points of the eleventh-round referee: $`\psi_{\Omega_2}(\Omega_2) + 1 \in C_0`$, so $`\omega^{\psi_{\Omega_2}(\Omega_2)+1} \in D`$; in FIXP the
  needed fact is that the least fixed point of $`\varphi_\delta`$ is $`\varphi_{\delta+1}(0) \gt \delta`$; UNIF-G is proved in two passes (first decide normal forms by
  induction on size, then compare them).
- **GAM-THETA′ and FIXP-Γ** (proved). $`\vartheta^\tau(\Omega_1^2 + \eta) = \Gamma_{b_\Gamma(\tau+\eta)}`$ for every $`\eta \lt \tau^\infty`$ (GAM-THETA was the part below $`\Gamma^{\mathrm{fp}}(\tau)`$), and
  $`\Gamma^{\mathrm{fp}}_2(\tau) = \vartheta^\tau(\Omega_1^2 + \Omega_1 + 1)`$. Wilken's base change between $`\upsilon`$-points keeps "Γ-fixed" in both directions.
- **PSI2⁺ and the InaccPsi side** (proved; the referee re-derived PSI2⁺ by hand at $`b = 0`$ and at $`b = \psi_{\Omega_2}(\Omega_2)`$).
  $`\psi_{\Omega_2}(\Omega_2 + 1 + b) = \Gamma_{\psi_{\Omega_2}(\Omega_2)+1+b}`$ for $`b \lt \psi_{\Omega_2}(\Omega_2\cdot 2)`$, and $`\psi_{\Omega_2}(\Omega_2\cdot 2) = \Gamma^{\mathrm{fp}}_2(\Omega_1)`$. EXACT-G⁺, COMP-G⁺, UNIF-G⁺,
  TERM-G⁺: EXACT-G, COMP-G, UNIF-G and TERM-G of §1 with $`\Gamma^{\mathrm{fp}}`$ of the base as one more atom.
- **Theorem NAME-OFFSET-G⁺** (proved). For every restart index $`\lambda`$ with $`\rho_\lambda \lt \upsilon^*`$ and $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$:
  $`c^+(\lambda) = (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$. This contains NAME-OFFSET-G of §1, and the offsets $`\psi_{\Omega_2}(\Omega_2) + c`$ of the referee's remark there.
- **The landmarks** (proved). The least restart with $`c^+ = \Gamma_{\Gamma^{\mathrm{fp}}(\rho)+1}`$ is $`H(\psi_{\Omega_2}(\Omega_2 + 1))`$; with $`c^+ = \Gamma_{\Gamma^{\mathrm{fp}}(\rho)\cdot 2}`$ it is
  $`H(\psi_{\Omega_2}(\Omega_2 + \psi_{\Omega_2}(\Omega_2)))`$; with $`c^+ = \Gamma^{\mathrm{fp}}_2(\rho)`$ it is $`H(\psi_{\Omega_2}(\Omega_2\cdot 2))`$; with $`c^+ = \Gamma^{\mathrm{fp}}_2(\rho) + 1`$ it is $`\Lambda_{\mathrm{fp}2}`$.
- **STRUCT″ and Wilken's claim on $`[0, \rho_{\Lambda_{\mathrm{fp}2}+\omega^2})`$ in $`R_2^C`$**, both halves (proved). STRUCT″ holds on this segment with every restart reach in
  closed form, and every ordinal below $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2\cdot 2)+1} + \omega^{\theta+2})`$ is in the core and is the value of an
  InaccPsi normal form with collapse arguments below $`I_\omega`$. Before: $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$. As in §1, the new fact for the claim is where this point lies.
- **VIS and PAR-ψ** (proved; the referee checked that the cited Lean lemmas of [InaccPsi](../../../Notation/InaccPsi/README.md), among them `KLt_complete` and
  `arg_mem_of_psi_mem`, exist and that their hypotheses match). If $`C_g \cap \Omega_1 = H(g)`$ and $`\tau \in C_g`$, then every countable maximal subterm of the normal
  form of $`\tau`$ is below $`H(g)`$.
- **L3, the shifted LOW-0** (proved, as a transfer of LOW-0 to the base $`\Omega_1`$, at the same standard as H3 of §1). A strictly increasing map $`E^{\Omega_1}`$
  from $`\theta`$ into $`T^{\Omega_1} \cap \Omega_2`$ whose parameters are among the countable maximal subterms and 0 (the paper says "are"; the referee: only "are
  among" is true, and only that is used). With H3: $`T^{\Omega_1} \cap \Omega_2 = \theta`$ exactly. (Erratum, [THETA.md](THETA.md) §9.1: only $`\le`$ is proved; nothing uses equality.)
- **B-PAR** (proved). The map $`B`$ of H3 sends every term of the simultaneous system of Weiermann–Wilken (MLQ 57, 2011) whose parameters are below
  $`H(g)`$ into $`C_g`$.
- **Not proved** (blocking point): Theorem THETA1, $`\Theta_1 = H(\theta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$ with $`\mathrm{lh}(H(\theta)) = H(\theta+\omega+1) + H(\theta+1)`$, and its
  bounds for $`c^+`$ below $`\Theta_1`$; Theorem THETA-A, $`\Theta_A = H(\varepsilon_{\theta+\omega}) = \psi_{\Omega_1}(\Omega_\omega + \varepsilon_{\theta+\omega})`$; so also the claim with the named end
  $`H(\varepsilon_{\theta+\omega} + \omega^2)`$, and "$`\nu_C`$ is above it". The proofs treat two notions of parameter as one: those of a term of Wilken's system
  (Wilken 2007, Defs 3.27, 5.1), which the base-change results of §1 use, and those of a term of the simultaneous system (Weiermann–Wilken 2011,
  Defs 4.7, 5.2), which $`B`$ and $`E^{\Omega_1}`$ control. That the two systems have the same values does not give this. The missing lemma, PAR-SAME, says
  that the two parameter sets of an ordinal are equal. The referee: it looks true and short (an induction along Def 3.2 of the 2011 paper, with
  Def 4.6 of Wilken 2007), and every other step of THETA1 and THETA-A is correct. The core half on $`[0, \rho_{\Theta_A+\omega^2})`$ was already proved
  (CORE-C$`^A`$, [PINS.md](PINS.md) §2); what PAR-SAME would add is the names. (The referee also asked that the map $`\Psi^\#`$ be used only where the
  parameters of its constants are below $`\rho_\mu`$, and that NU-CT, not an $`R_2^S`$ result, be cited for $`\nu_C`$.) **Now proved**: PAR-SAME, and with it THETA1 and
  THETA-A (2 reviews, [THETA.md](THETA.md) §1).
- **The hull lemma** (H2a), (H2b) of §1. With PAR-SAME it is not needed for $`\Theta_1`$; it would give only the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and
  $`\Theta_1`$. The paper's proof of it below $`\psi_{\Omega_2}(\Omega_2\cdot 2)`$ is an outline of a transfer (the referee: plausible; nothing uses it). Beyond that it is open.
- **Not counted**: NEST-UP and NEST-CHAR (proved, but the referee finds that together they restate $`\nu_C = T_C`$, the least top of a nested pair,
  [BREAK.md](BREAK.md) §2): $`\nu_C`$ is the least right end $`b`$ of a pair $`a \lt_2 b`$ with pairs cofinal below $`a`$. (The fact needed in $`R_2^C`$ is NU-CT, not the
  $`R_2^S`$ result that the paper cites.)
- **Open**: an InaccPsi upper bound for $`\nu_C`$ (one positive $`\lt_2`$-relation at a named point, whose left end is a restart with pairs cofinal below it);
  the names of $`\Theta_\delta`$, $`\Theta_{d\omega}`$ and $`\Lambda^*`$, which need maps like $`B`$ and $`E^{\Omega_1}`$ at other bases. (Now these maps exist at the bases
  $`\psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$, and lower bounds for these names are proved as a transfer, [THETA.md](THETA.md) §1; now the names are proved, §9.1 there.)

## 9. Native codes up to $`\Phi_1`$

Notation of §2. $`\Xi_\alpha`$ is the $`\alpha`$-th nonzero fixed point of $`\zeta \mapsto \upsilon_\zeta`$, and $`\Phi_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$ is the least fixed point of
$`\alpha \mapsto \Xi_\alpha`$ (Theorem T++, [REACHES.md](REACHES.md) §2; the paper does not use these names in its proofs). A layer is $`[\upsilon_\zeta, \upsilon_{\zeta+1})`$; its
ordinals are values of Wilken's terms over the base $`\upsilon_\zeta`$ with parameters below the base.

- **REL and STEP-IN** (proved). Over every base, with any closed set of outer parameters held fixed, the four local steps inside a layer hold in the
  strong form: the copy fixes the outer parameters and puts the new chain just below the root. The three cases that the eleventh-round referee
  checked by hand are written out. So **IDX-REF** of §2 holds without its caveat (2 reviews). (The referee: the relative arithmetic is never run
  numerically, and the steps that start at the base of a layer itself need one more sentence.)
- **The layered codes** (proved: FIN-N, PAT-N, DROP, KIND, EXIST-AMB, UNIV-B, PLACE-AMB). Each layer gets one module, the code of the index of its base. The
  parameters of a code are points and modules of lower layers, nested to any depth. Every code is a finite L1p-free RF fan-free pattern. (The referee:
  one case of PLACE-AMB, a new fixed module below a host that is not fixed, is not written; it never occurs, and the proof should say why.)
- **Theorem IDX-Y** (proved). $`N(\gamma') \ll N(\gamma)`$ for $`\omega \le \gamma' \lt \gamma \lt \Xi_1`$. With HOST2: $`\iota(\mathrm{CH}_2) \ge \Xi_1`$. Without nested parameters the order type stops at
  $`\upsilon_2^\omega`$.
- **Blocks, and Theorem IDX-XI** (proved: CHAIN, RANK, RANK-HOST). A block of rank 0 is the pattern of SRO[0], of rank 1 a block G, of rank $`1 + \sigma`$ a block
  SRO$`_\sigma`$ (SRO$`_1`$ is the pattern of SRO). A block hosts every ordinary chain with small increments and every block of smaller rank. The fixed point
  $`\Xi_{\lambda+\omega^\kappa}`$ gets as module the code of $`\Xi_\lambda + 1`$ followed by a block of rank $`\kappa`$. Then $`N(\gamma') \ll N(\gamma)`$ for $`\omega \le \gamma' \lt \gamma \lt \Phi_1`$, so
  $`\iota(\mathrm{CH}_2) \ge \Phi_1`$; the pattern of SRO[0] lies above every code of an index below $`\Xi_1`$, and the pattern of SRO above every code of an index below $`\Xi_{\omega^2}`$.
  (The referee: one step uses PLACE-AMB for a set that ends in a block and so is not a code; the proof carries over word for word. In EXIST-AMB one bound is
  given a reason that holds only for a point host; for a module host it holds because the bound lies below the next layer.)
- These bounds are native: they come from codes, not from reaches. The referee: they are far below the known $`\iota(\mathrm{CH}_2) \gt \nu_C \gt \Lambda_\varepsilon`$; the progress is
  on the route toward $`\iota(\mathrm{CH}_2) \ge \theta_0`$ only.
- **Not proved**: $`\iota(\mathrm{CH}_2) \ge \theta_0`$, as the paper says. The gap is a native family of order type $`\theta_0`$. This family already spends SRO (which conv
  reads as $`\theta_0`$) at the index $`\Xi_{\omega^2}`$; the next kind of block is an outline only, and a grammar that follows conv (with codes for the collapse
  arguments too) is open. Also not proved: "the codes are cofinal below the pattern of SRO[0]"; only "below" is proved.

## 10. The shapes of $`\Phi_3`$: sibling copies ($`t = 0`$)

Notation of §3. For $`t = 0`$ with the bad root $`R`$ not a root column, the parent of $`R`$ has in $`A[n]`$ the children $`K`$ followed by $`n + 1`$ copies of
the subtree $`S`$ of $`R`$: the copies are siblings.

- **Lemmas NF, SEQ-N and FAM** (proved; FAM for the families that the program creates). A run symbol stands for $`K`$, then $`S^{j+c}`$, then a suffix, for
  every $`j \ge J_0`$ at once, inside children tuples and sums; runs may be nested. Normal forms of runs are unique, and a walker compares words with
  nested runs for every $`j`$ at once. (The referee: the program misses one case of a family, when it starts at once; it occurs in none of 1,764 symbolic
  runs, and the validation would reject it.)
- **Lemma SYM-R** (proved given (REP)). The program is rewritten in memory by seven rules, each the original code on concrete input; a finishing
  symbolic run gives the concrete run for every $`j \ge J_0`$. (REP) says that the run does not depend on how objects are stored and shared, which
  decides the program's identity tests. (REP) is checked (by the referee up to $`j = 20`$), not proved. The referee: it is used more widely than it is
  stated, and the symbolic entries since [FANFREE.md](FANFREE.md) §10.1, those of §3 among them, carry the same condition.
- **Theorem SH0-A** (proved given (REP)), with **Lemma BASE-PHI-U** (proved): one template for every $`n`$, and FS⁺ for every $`n`$ from BASE-PHI checked once on the
  template. 234 matrices (19 of them were proved only given LOW before).
- **Theorem PER0** (proved given (REP)) with **Lemma STEP-PHI** (proved): the run in the children of the root, with the chain of anchors as the black box.
  178 matrices. **Corollary SUM-CORE0** (proved): 8 matrices.
- **Lemmas BASE-PHI-R and DIRECT-R** (proved). For $`t = 2`$, each gives FS⁺ at one level $`n`$, for a chain of any length. The shape for every $`n`$ is open.
  (The referee: the check of DIRECT-R lets the point lie in the root block, which the text excludes; the proof is valid either way, and only the counts
  checked for small $`n`$ are affected. The fact that a left end of $`\lt_2`$ is additively principal needs Carlson 2009, Def 5.6, together with L.5.5(6).)
- **The tally** (the referee checked the counts):

| class | matrices | proved for every $`n`$, given (REP) | given LOW | given a condition checked for small $`n`$ | $`t = 2`$, derivation checked for $`n \le 7`$ | open |
|---|---|---|---|---|---|---|
| I | 581 | 381 | 2 | 0 | 0 | 198 |
| SUM | 603 | 488 | 0 | 7 | 0 | 108 |
| ROOT | 635 | 491 | 0 | 0 | 87 | 57 |
| III | 1,347 | 502 | 0 | 0 | 53 | 792 |
| all | 3,166 | 1,862 (before: 1,442) | 2 | 7 | 140 | 1,155 |

- **Open**: UNIF-FS below SRO. The 1,304 matrices that are not proved:

| class | matrices | why it is open |
|---|---|---|
| $`t = 0`$, M1 | 258 | the $`\omega`$-run fold of the reach; the block per step is not fixed (nested blocks) |
| $`t = 0`$, M2 | 139 | anchors peeled inside the closure: families of one-term nodes |
| $`t = 0`$, M3–M5 | 65 | a low template outside the image (28), interleaved families (14), PER0 fails, short bodies or identity of run copies (23) |
| $`t = 2`$ | 460 | 140 with the derivation checked for small $`n`$; 320 where it fails at some $`n \le 5`$ (all of I and SUM among them: they need a lifting of the core) |
| $`t = 1`$ | 382 | as in §3: III with the bad root in the $`\Omega`$-level structure 201, other 140, ROOT 17, SUM 24 |

## 11. $`\nu_C = \nu_S`$: the corrected residue

Notation of §4 and of [FANFREE.md](FANFREE.md) §10.3 ($`u^\#`$, $`D^\#_n`$, the maps $`T_n`$). $`u_m = \upsilon^2_m`$. $`P^*`$ is an isominimal set with $`x, \nu \in P^*`$,
$`X = P^* \cap [x, x^\#)`$, and $`\tilde X`$ is its downward copy, with $`\tilde x = u_m`$. (HC) says that the hereditary parameters of $`X`$ are below $`u_m`$.

- **RED$`_T`$** (proved as an implication). The corrected reduction of §4: with any finite set $`T \lt \tilde x`$ held fixed and closed extension sets, (LOC$`_T`$)
  and (TR$`_T`$) give $`\nu_C = \nu_S`$. But (TR$`_T`$) fails whenever $`P^*`$ has a point in $`[x^\#, \nu)`$, which is the setting of the results below (see **Not proved**).
- **ISO-COV, AP2, LH#** (proved). An isominimal set is pointwise below every closed covering of itself; a proper $`\le_1`$-left end is indecomposable, and
  below $`\nu`$ both ends of a $`\lt_2`$-pair are $`\upsilon`$-points; $`\mathrm{lh}(z) \lt u^\#`$ for $`z \in (u, u^\#)`$.
- **COPY-EQ and LOC#** (proved given (HC), which is open). The downward copy is the image under the map of [FANFREE.md](FANFREE.md) §10.3:
  $`\tilde X = T_{x\to u_m}[X]`$ (two coverings and isominimality, in the style of Carlson 2009, the proof of L.15.7). Then (LOC$`_T`$) holds there, with $`T_m`$ as the map.
- **CROSS** (proved). Every $`\le_1`$- or $`\le_2`$-relation between a low point and a point above the copy is the same on both sides.
- **ET-TF** (proved). Under (HC), with $`Y \subset [x, x^\#)`$ and $`x^\# \in P^*`$: every extension of the copy of $`Y`$ whose closure has no sum $`z + w`$ with $`z \ge u_m^\#`$ and
  $`0 \lt w \lt u_m^\#`$, $`w \notin P^*`$, is realized over $`Y`$ below $`\nu`$ with the same diagram. (The referee: the reason given for one case of sums is wrong, since a low
  summand can be a suffix of a point of $`P^*`$ without being in $`P^*`$; the case holds by Cantor normal form arithmetic. AP2 and COPY-EQ should cite Carlson 2009, L.5.5(7).)
- **Example TW** (proved). For $`a = \upsilon_\iota`$ with $`\iota = u_{m+1} + \omega^{u_m}`$: $`\mathrm{lh}(a) = \delta_\iota + \tilde x`$, but the upward copy $`a^{**}`$ has $`\mathrm{lh}(a^{**}) \lt \delta^{**} + x`$. So the
  copy that Carlson's upward rule gives breaks a $`\le_1`$-relation that a translation needs.
- **Not proved**: GHOST-TR as stated (a boundary case at $`u_m^\#`$; with the referee's fix, terms $`\ge u_m^\#`$ in place of $`\gt u_m^\#`$, it holds); TR-RED, "(TR$`_T`$) is
  exactly a condition on reach tails" (the low part of a sum can lie outside the set); "Carlson's rules cannot give (TR$`_T`$)" (Example TW shows only that
  one image fails); and (blocking point) "(R1)–(R3) below give $`\nu_C = \nu_S`$". For $`e = \max\tilde X + \tilde x`$ every extension must send $`e`$ to $`\max X + x \lt x^\#`$, below
  the points of $`P^*`$ in $`[x^\#, \nu)`$, so (TR$`_T`$) fails; and (R3) does not control the sums $`B + q`$ with $`q \in P^* \cap x`$. The referee's repair (not written): a
  reduction in the form of ET-TF, with the reach-tail condition for every nonzero low part.
- **Open**: (R1) (HC) for some isominimal $`P^*`$; (R2) the local part when $`Y`$ meets $`[x^\#, \nu)`$ (it needs the maps beyond $`D^\#`$: (PROF) and zone C); (R3) a
  "twisted" upward rule that moves the reach tails of the points above the copy; and $`\nu_C = \nu_S`$ itself.

## 12. Status after the twelfth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, \rho_{\Lambda_{\mathrm{fp}2}+\omega^2})`$, with the reaches there in closed form (§8). $`\Theta_1 = H(\theta)`$ and $`\Theta_A = H(\varepsilon_{\theta+\omega})`$
  need only the lemma PAR-SAME.
- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 1,862 of the 3,166 sample matrices, given (REP) (§10); the native
  codes are ordered on $`[\omega, \Phi_1)`$, so $`\iota(\mathrm{CH}_2) \ge \Phi_1`$ natively (§9).
- The first inaccessible: $`H_m`$ is open; it would follow from $`\iota(\mathrm{CH}_2) \ge \theta_0`$.
- Upper bounds: no InaccPsi bound is proved for any $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: given (HC), the downward copy is the copy by $`T`$, the local part holds, and every extension without such translations is realized
  (§11); the reduction to (LOC$`_T`$) and (TR$`_T`$) does not work there. Left: (R1)–(R3) and a reduction in the form of ET-TF.

The thirteenth to thirty-seventh rounds changed this status; see [THETA.md](THETA.md) §5, §9.5, [SHIFT.md](SHIFT.md) §5, §8.5, §9.5, [SHIFT2.md](SHIFT2.md) §1.5, §2.5, §3.5, [SHIFT3.md](SHIFT3.md) §1.5, §2.5, [SHIFT4.md](SHIFT4.md) §1.5, §2.5, [SHIFT5.md](SHIFT5.md) §1.4, §2.4, [SHIFT6.md](SHIFT6.md) §1.4, §2.4, §3.4 , [SHIFT7.md](SHIFT7.md) §1.4, §2.4, §3.4, [SHIFT8.md](SHIFT8.md) §1.4, §2.4, [SHIFT9.md](SHIFT9.md) §1.4, §2.4 and §3.4.

## 13. Checks of the twelfth round

Each run was under 60 seconds; none is a proof. Certificates count only when replayed.

- Offsets and parameters (§8). $`E^{\Omega_1}`$ on 2,998 terms and 998,543 pairs: 0 order or domain failures; three deliberately broken versions all fail. $`B`$
  keeps parameters on 3,352 pairs; PAR-ψ agrees with the Lean comparison on 5,400 pairs. PSI2⁺ and UNIF-G⁺ at 3 bases (57,360 comparisons): 0 mismatches.
  The 24 named points are normal forms and strictly increasing (Python, and a Lean test file, green). The referee: the same results on a rerun with
  four seeds; an own adversarial test with 31 countable atoms (1,793 terms, 558,245 pairs): 0 failures; PAR-ψ on 12,551 pairs: 0 disagreements; the Lean
  file green again. PAR-SAME cannot be tested here, because Wilken's system has no implementation.
- Codes (§9). 258,648 codes are L1p-free RF fan-free patterns; in 169,227 random steps every new parameter gets a host of the claimed kind, 0 failures;
  11 certificates in the predicted direction, all replayed; none in 3 reverse searches. The referee: 19 searches against the claimed order found
  nothing (each stopped at about 45 s), and 3 new certificates in the claimed direction were replayed. This is weak evidence: the searches are shallow,
  and no copy, chain or rank step is run.
- Shapes (§10). Every acceptance equals the concrete conv for $`j = 3, \ldots, 9`$; 752 random acceptances outside the sample are valid. The referee: $`j`$ up to 20
  on all 234 + 178 matrices, 0 differences, and a planted mismatch is caught; SEQ-N on 116,197 comparisons with nested runs, 0 wrong; the $`t = 2`$
  derivation up to $`n = 7`$ on all 140; 283 new random matrices valid up to $`j = 15`$.
- $`\Sigma_2`$ (§11). The paper ran nothing. The referee's toy model of Cantor normal forms shows the failure of (TR$`_T`$) (6 of 6 forced images below $`x^\#`$) and
  the gap in TR-RED.

## 14. Open

The thirteenth to thirty-seventh rounds changed this list; the current list is [SHIFT9.md](SHIFT9.md) §3.6.
