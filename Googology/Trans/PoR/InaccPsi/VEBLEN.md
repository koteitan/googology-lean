[← Back](README.md) | [English](VEBLEN.md) | [Japanese](VEBLEN-ja.md)

# $`R_2^+`$, the eleventh round: offsets past Γ, native codes up to $`\upsilon_1`$, a periodic symbol for the shapes of $`\Phi_3`$, and a direct $`\Sigma_2`$ argument

This page continues [FANFREE.md](FANFREE.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from 2026-10; they come from
the eleventh round of four papers. A statement with a blocking point against it is listed under **Not proved**; a statement that its
referee found to restate the target, or to be trivial, is listed under **Not counted**. A certificate counts only when it was replayed.
None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009,
p. 97, announces. No result on this page is in Lean, and no Lean file was added. The notation is that of [FANFREE.md](FANFREE.md).

Four papers, each refereed once, so every result here has 1 review. One paper (§1) checked a Lean test file of named points with
leanman (green, and green again in the referee's rerun); that file only compares terms (`#eval`, no theorem), and it is not added to
the library. The other three papers make no Lean claim. The papers number the levels one lower; here they are renumbered (a point of
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
  VEB-THETA are only asserted); no proved result uses it.
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
  3,166 matrices built in three ways, 0 differences.
- $`\Sigma_2`$ (§4). The paper ran nothing. The referee checked one fact on sums used in TOP on 93,411 random cases below $`\omega^\omega`$, 0 failures.

## 7. Open

- The first inaccessible: $`H_m`$ (equivalently, some $`\iota(\mathrm{CH}_k) \ge \theta_0`$; enough: $`\iota(\mathrm{CH}_2) \ge \theta_0`$, from a map $`\nu`$ on all of $`D`$ with L1p-free
  values and $`\nu(s) \ll \nu(t)`$ at every step); UNIF-FS below SRO on the open classes of §3; codes with nested references and the block
  grammar of the $`\Omega`$-levels (§2); $`\iota(A_n) \ge |\tau_n|`$.
- Upper bounds: any InaccPsi bound for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, or for $`\nu_C`$; STEP-CH (on a class closed under $`\Phi`$, with collapse arguments
  below $`I_0`$); REL-SHARP; (HQ).
- Names and offsets past $`\Lambda_{\mathrm{fp}}`$: (H2a) and (H2b) beyond $`\psi_{\Omega_2}(\Omega_2)`$, which give $`\Theta_1 = H(\theta)`$; the names of $`\Theta_A`$, $`\Theta_\delta`$,
  $`\Theta_{d\omega}`$, $`\Lambda^*`$, $`\nu_P`$; whether $`\nu_C \lt \upsilon^*`$.
- $`\nu_C = \nu_S`$: (LOC) and (TR) with a fixed finite set below the copy (§4); (PROF); the reaches at limits of fixed points of $`k`$; $`Y \subset S_\omega`$
  beyond $`[x, x^\#)`$.
- The rest of [COVER.md](COVER.md) §9.
