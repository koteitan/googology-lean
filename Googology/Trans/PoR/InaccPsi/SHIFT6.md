[← Back](README.md) | [English](SHIFT6.md) | [Japanese](SHIFT6-ja.md)

# $`R_2^+`$, the twenty-seventh round: $`\nu_C \ge X_{22}`$ given FRAG, exact long reaches below $`G(\hat\zeta_3)`$, the cushion cap, the moved-lower pin, and native codes up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$

This page continues [SHIFT5.md](SHIFT5.md) (§2 there is the twenty-sixth round); §1 is the twenty-seventh round. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

## 1. The twenty-seventh round

Three papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-sixth round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. Papers cited: [W07b] (L.2.1, Thm 2.2,
the proof of Thm 5.3) in §1.1; no paper is used in a proved step of §1.2 or §1.3 (§1.3 quotes Carlson 2001 in a remark only, and does not use FRAG). No Lean file
was added: the papers of §1.1 and §1.3 checked a Lean file that only compares terms (`#eval`, no theorem; green, and green in the referees' reruns), so these count as checks;
§1.2 has no Lean file. The minor points of the twenty-sixth-round reviews ([SHIFT5.md](SHIFT5.md) §2) are applied: those of §2.1 there by the paper of §1.1, those of §2.2 by §1.2
and those of §2.3 by §1.3, and their referees checked them again (**2 reviews**). Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher than in the papers): level 1 is below
$`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, and level $`1+\xi`$ holds the restarts $`H(\Omega_\omega\cdot\xi + \eta')`$ with $`0 \lt \eta' \lt \Omega_\omega`$.

Names of [SHIFT5.md](SHIFT5.md): $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$, $`G_2 = G(\omega^2)`$, $`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$, $`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$,
$`\hat\zeta_3 = \theta_3\cdot\omega^2`$, $`\hat\zeta_G = \theta_3\cdot\Omega_3`$, $`\hat\zeta_A`$, $`\hat\zeta_H`$, $`\hat\zeta_f`$, $`\hat G = G(\Omega_2)`$, $`F_\lambda = H(\eta_\lambda + \Omega_1)`$, the reading $`R`$, $`u_4 = H(\Omega_4)`$ and $`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$.
New names of this round:

```math
\theta_4 = \psi_{\Omega_5}(\Omega_\omega),\qquad \mathrm{st}(T) = \psi_{\Omega_1}(\Omega_\omega\cdot T),
```

with $`R(\theta_4\cdot\omega^2) = G(\hat\zeta_3)`$, $`\hat\zeta_H \lt \Omega_4 \lt \theta_4\cdot\omega^2 \lt \Omega_5`$ and $`G(\hat\zeta_3) \lt G(\Omega_4) \lt G(\theta_4\cdot\omega^2) \lt P'`$ (checked); $`\mathrm{st}^n`$ is the $`n`$-th iterate of $`\mathrm{st}`$.

### 1.1 PSI-θ past the index $`\theta_2+1`$, exact long reaches below $`G(\hat\zeta_3)`$, and the cushion cap: $`\nu_C \ge X_{22}`$ given FRAG

- **The minor points of the review of [SHIFT5.md](SHIFT5.md) §2.1 are applied** (proved, **2 reviews**). The step "the supremum is at most $`F_\lambda`$" of THETA$`^G`$ is now the referee's induction;
  the forms at uncountable multipliers cite PSI-n with a high part and the covering lemma of the codes, and "onto" is claimed only below $`\pi_\eta`$; the reading stays in the hull; the targets of
  EXACT-LONG$`^G`$ and EXACT-F come from TOP-REG-LAND; the ceiling at $`\hat\zeta_A`$ is proved; NO-READL rests on EXACT-LONG$`^G`$ and EXACT-F; the value of the cap does not depend on how the remark on
  "the maximum of the landings" is read. So the claim on $`[0, X_{21}]`$ given FRAG now has **2 reviews**.
- **PSI-θ$`^{(3)}`$** (proved by transfer). The counting rule for $`\psi_{\Omega_2}`$ holds for every normal form $`\psi_{\Omega_2}(\Omega_\omega + \zeta_H + \delta)`$ with $`\zeta_H`$ a multiple of $`\Omega_3`$ below
  $`\hat\zeta_G`$ and $`\delta \lt \Omega_3`$: the same proof as PSI-n one step down, on top of the refereed counting rule for $`\psi_{\Omega_3}`$. So the rule PSI-θ now holds at the index $`\theta_2+1`$,
  which the twenty-sixth round lacked, and at every index below $`\psi_{\Omega_3}(\Omega_\omega + \hat\zeta_G)`$. For every normal multiplier $`\zeta \lt \hat\zeta_G`$, $`G(\zeta+1)`$ is the next element of the class $`C_{\theta_2}`$ of the rule
  after $`G(\zeta)`$, so every code in $`[G(\zeta), G(\zeta+1))`$ has a form over the base $`G(\zeta)`$.
- **THETA$`^{(3)}`$, EXACT-LONG$`^{(3)}`$, MONO-L$`^{(3)}`$, LAND-B** (proved by transfer, given FRAG). The native reading $`\Theta_\lambda`$ is defined on every code below $`G(\hat\zeta_3)`$ (below $`\pi_{\eta_\lambda}`$); it maps
  them onto $`[0, H(\eta_\lambda + G_2))`$ and commutes with the transports, with $`\Theta_\lambda(G(\zeta)) = H(\eta_\lambda + 1 + R^\Theta_\lambda(\zeta))`$ ($`R^\Theta`$ the reading with constants read by $`\Theta_\lambda`$; the readings in the base $`\hat G`$
  at $`F_\lambda`$ are the case $`\zeta = \Omega_2`$). So a long restart with code $`G_2\cdot D + m_0`$ has its exact reach for every $`D \lt G(\hat\zeta_3)`$ (before: $`D \le \hat G`$). Its landing η-offset is below $`G_2`$
  and has only short prefixes, so nothing overshoots. The reach is strictly increasing in the code, and every restart with code below $`G(\hat\zeta_3)`$ reaches below $`H(\eta + G_2)`$.
  (The referee: the paper writes the bound of LAND-B with "$`+1`$", which is false as written; with "$`+\omega^2`$" every use holds.)
- **FAR-PIN$`^{L3}`$, OWN-PREFIX$`^f`$** (proved by transfer, given FRAG). Every code below $`G(\hat\zeta_3)`$ is an exact atom for the far pins. At $`\hat\zeta_f`$ the restart's own prefix of code $`\hat G + G_2`$ lands $`\Omega_1 + \omega^2`$
  further on, so READ$`^L`$ fails there by this prefix as well, and the hull cap CAP$`^\sharp`$ holds on that family. (The referee: the limit step at $`\hat\zeta_H`$ must be written out.)
- **CUSHION** (proved by transfer, given FRAG). A cap that needs no hull. Let $`\lambda`$ be a restart with code $`m`$ in $`[G(\zeta), G(\zeta+1))`$, $`G(\hat\zeta_3) \le m \lt G(\theta_4\cdot\omega^2)`$, and let $`C`$ be the sum of the
  terms of $`R_\lambda(\zeta)`$ with exponent $`\ge G_2`$, plus $`G_2`$. With the cap reading $`\Phi_\lambda`$ of [SHIFT2.md](SHIFT2.md) §2.1:

```math
r(\lambda) \lt H(\eta_\lambda + C + \omega^2\cdot\Phi_\lambda(m) + \omega^2).
```

  Every landing of a code below $`G(\hat\zeta_3)`$ lies less than $`G_2`$ beyond its own prefix, so the term $`G_2`$ absorbs every overshoot, and $`\omega^2\cdot\Phi_\lambda(m)`$ separates the codes.
  (The referee: the paper writes "$`+1`$" for "$`+\omega^2`$" here too; and in the arithmetic lemma "prefix" must be "proper prefix".)
- **Corollaries** (proved by transfer, given FRAG). **CAP-0 for every code below $`G(\theta_4\cdot\omega^2)`$** (before: below $`G(\hat\zeta_H)`$): every multiplier in $`[\Omega_3, \Omega_4)`$, the plateau top $`u_4`$, and the multipliers in
  $`[\Omega_4, \theta_4\cdot\omega^2)`$. **$`u_4`$ is not self-crossing**, with no hypothesis, so case (ii) of DICHOTOMY-4″ never happens. LONG-CLASS$`^{22}`$: $`r(\lambda) \ge H(\eta_\lambda + G(\hat\zeta_3))`$ implies
  $`m_\lambda \ge G(\theta_4\cdot\omega^2)`$. LOW-RED$`^{22}`$: LOW$`_x`$ implies cofinally many self-crossing long restarts below $`x`$ with codes in $`[G(\theta_4\cdot\omega^2), P')`$.
- **Theorem X22** (proved, given FRAG):

```math
\nu_C \ge X_{22} = \psi_{\Omega_1}(\Omega_\omega + \theta_4\cdot\omega^2 + \omega^{G(\theta_4\cdot\omega^2)+1}\cdot 2),\qquad G(\theta_4\cdot\omega^2) = \psi_{\Omega_2}(\Omega_\omega + \theta_4\cdot\omega^2).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{22}]`$, both halves, given FRAG**, $`\nu_S \ge X_{22}`$, and $`X_{21} \lt u_4 \lt X_{22}^- \lt X_{22}^\natural \lt X_{22} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (checked, Python and Lean).
With fewer of the new tools the same proof gives the fallbacks $`X_{22}^\natural`$ and $`X_{22}^-`$: $`\theta_4\cdot\omega^2`$ replaced by $`\Omega_4 + \psi_{\Omega_4}(\Omega_\omega + \Omega_4)`$ and by $`\Omega_4 + \theta_3`$. Also (P-LOW$`^{22}`$)
every restart $`a`$ with $`H(\theta_2\cdot\omega^2) \lt a \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ and (P) at $`(a, b)`$ has $`m_a \ge G(\theta_4\cdot\omega^2)`$. (The referee: one step should say that the region hypothesis of
CUSHION holds there.) **Conditional, not counted**: under not-LOW, $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\theta_4\cdot\omega^2)+1})`$.

- **Not proved** (blocking point; X22 does not use it): EX-RED, "exact atoms for every code below $`G(\Omega_k)`$ give CAP-0 below $`G(\Omega_{k+1})`$", and with it "not-LOW follows if every code below $`P'`$
  has an exact atom". The proof puts $`\omega^{G(\Omega_{k-1})+1}`$ in place of $`G_2`$; then the last term of the cushion has code $`G(\Omega_{k-1})+1`$, whose landing offset is uncountable ($`Z`$ for $`k = 4`$), so its atom
  lies above every possible target (the referee's test). The referee's possible repair (not checked): a stronger hypothesis "landing below $`R(\zeta) + \Omega_1`$" and a finite descending chain of
  cushion terms down to $`\omega^{Z+1}`$.
- **Open**: where the cushion stops. At $`\theta_4\cdot\omega^2`$ the reading is $`G(\hat\zeta_3)`$; up to $`\theta_4\cdot\omega^2 + \omega^{\psi_{\Omega_3}(\Omega_\omega + \theta_4\cdot\omega^2)+1}`$ the cushion extends in outline. The first code without a separating
  atom is $`G(\hat\zeta_3) + 1`$: there the landing cap gives only an upper bound, and the matching lower bound (EXACT-LAND) is open. The two-sided hull cap from $`G(\hat\zeta_A)`$ on, at $`\Omega_k`$
  ($`k \ge 5`$) and at $`\Omega_\omega`$: open. LOW: open.
- The referee's other minor points: the step from the ceiling to $`\eta \ge \theta_2\cdot\zeta`$ needs one more line; the paper's label "proved (the obstruction)" should be "remark"; the docstring of
  one script is out of date.

### 1.2 $`\nu_C = \nu_S`$: the moved-lower pin, and base change for every code below $`\varepsilon_{\hat G+1}`$

Notation of [SHIFT5.md](SHIFT5.md) §2.2; LOW$`^\infty`$ is $`\nu_C \lt \upsilon^\infty`$.

- **The minor points of the review of [SHIFT5.md](SHIFT5.md) §2.2 are applied** (proved, **2 reviews**): the blocking point of the old route is replaced by LOW$`^\infty`$, not lifted; the audit
  rows for the cap of the θ tier and for the transport templates are written, and every place that depends on η is one of the six known kinds (the referee spot-checked three rows);
  the missing case of the cross-level base change; code 0 gives no restart; the side correction of EXACT-CL\* ([SHIFT4.md](SHIFT4.md) §2.1).
- **BC$`^{\mathrm{mv}}`$, THETA-EQ$`^{\mathrm{mv}}`$, MRC$`^{\mathrm{mv}}`$, PIN-ALL$`^{\mathrm{mv}}`$, LPIN$`^{\mathrm{mv}}`$** (proved, given FRAG; this repairs the blocking point of [SHIFT5.md](SHIFT5.md) §2.2). The pin works at a base restart $`\nu`$
  whose image is any restart and whose lower parameters are moved, where only $`h \ge T`$ is known: the first step is a far pin (not PIN-IDX), the moved lower atoms are handled with
  $`h \ge T`$, and the induction runs on the offset. So the landing restart of a long prefix is pinned even when its code has atoms in moved regions, for every $`D \lt \varepsilon_{\hat G+1}`$.
  (The referee: the key step has a refereed precedent, FAR-PIN$`^L`$ of [SHIFT5.md](SHIFT5.md) §1.1; the moved set must be closed under Cantor normal form terms and exponents; the
  hypothesis that the base has a large index exponent must be stated, and it holds at the only use.)
- **PIN$`^{(2)}`$ without the restriction**: **not proved as stated** (the paper says the old pin lemma holds as stated, but its proof needs $`h \ge T`$ also on the hereditary parameters
  of the atoms). **Conditional, not counted** (correct under LOW$`^\infty`$, given FRAG): with that hypothesis supplied by the simultaneous induction, TOP-REG$`^{T2}`$, PLACE$`^{T2}`$, RES-ALL$`^{T2}`$
  and the reduction of [SHIFT5.md](SHIFT5.md) §2.2 hold with no restriction on the atoms.
- **The twenty-sixth-round tools at every level** (proved by transfer, given FRAG): THETA$`^G`$, EXACT-LONG$`^G`$, EXACT-F, the landing and hull caps below $`G(\hat\zeta_H)`$ and LONG-CLASS$`^{21}`$ hold at
  every level $`\ge 1`$.
- **THETA$`^e`$, EXACT-LONG$`^e`$, TC⁺$`^e`$, MONO-F$`^e`$** (proved, given FRAG). EXACT-LONG$`^G`$ and EXACT-F cover only the codes below $`\hat G + G_2`$, since $`G_2\cdot\hat G = \hat G`$. New: the Cantor
  normal form over $`\hat G`$, read at $`F_\lambda`$. For every $`D \lt \varepsilon_{\hat G+1}`$ a long restart lands at an η-offset $`\Omega_1 + x`$ with $`x`$ countable, and its reach is exact; $`r(BR) = B(r(R))`$ for
  every base change $`B`$ between restarts at any levels and every restart $`R`$ with code below $`\varepsilon_{\hat G+1}`$. So **reaches commute with base change for every code below $`\varepsilon_{\hat G+1}`$, at
  every level** (before: below $`G_2^2`$). (The referee: "onto" needs $`\pi_\eta \gt \hat G`$; it fails at some restarts of level 1 with $`\pi_\eta \lt \hat G`$, such as $`\eta = \omega^2`$; every use has a code $`\ge \hat G`$.)
- **Conditional, not counted** (correct under LOW$`^\infty`$, given FRAG): with READ$`^\sharp`$ below $`G(\hat\zeta_H)`$ at every level, every (D1b) span whose bottom has code below $`G(\hat\zeta_H)`$, and every
  span whose η-offset is below $`\varepsilon_{\hat G+1}`$, is placed; the room reaches the offsets below $`G(\hat\zeta_H)`$; the zone becomes $`H(\eta_u + \varepsilon_{\hat G+1})`$; and the inspection after TWIST,
  now written line by line, holds (the referee: one use, that the zone lies below the next point, is not a zone axiom; it holds here).
- **REDUCTION$`^{(4)}`$** (proved as a conditional). $`\nu_C = \nu_S`$ follows from FRAG, LOW$`^\infty`$ and three open items: (R1″) exact landing reaches for the codes in $`[\varepsilon_{\hat G+1}, \Omega_2)`$
  and for the restarts with $`\tau \ge \Omega_2`$ (the Veblen tier over $`\hat G`$ is only an outline); (R2″) caps for codes $`\ge G(\hat\zeta_H)`$, needed only for spans with η-offset $`\ge G(\hat\zeta_H)`$; (R5) the zone past
  $`H(\eta_x + G(\hat\zeta_H))`$ (new). The inspection after TWIST is no longer an input. $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$ are both **open**.
- The referee's other minor points: codes below $`G(\Omega_3+1)`$ need the cap clause of LONG-CLASS$`^{21}`$, not READ$`^\sharp`$; one sentence is redundant; the author's test of the landing offsets
  covered only offsets below $`F`$, and the referee's test covers the offsets built from $`F`$.

### 1.3 Native codes: stage labels made of whole lower codes, and $`\sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$

Words of [SHIFT3.md](SHIFT3.md) §1.2, §1.3 and [SHIFT5.md](SHIFT5.md) §2.3: stages, pair blocks, chain number, decorations, module systems.

- **The minor points of the review of [SHIFT5.md](SHIFT5.md) §2.3 are applied** (**2 reviews**): the base step uses the systems below each $`Z_n`$ one by one; the carrier of a copied label is the point
  $`p`$ of the larger label, and the copy lies above $`b`$; the weights are dropped and the closure of old and new elements is stated; the second pair is "not needed"; the comparison of $`\mathrm{CH}_3`$ and $`\mathrm{CH}_4`$ cites
  HOST$`_4`$; Carlson 2001 only announces the identification.
- **The ordinal side for every countable stage** (proved by transfer). The counting rule for $`\psi`$ over $`\Omega_\omega`$ and the parameter lemmas of [SHIFT3.md](SHIFT3.md) §1.2–§1.3 hold for every countable
  stage $`T`$. At the lowest level the parameter lemma holds only in one direction, which is the only one used (the referee: the other direction fails, for example at $`T = \varepsilon_0`$).
- **BELOW-σ, FIX-σ, PUSH$`^S`$** (proved). With $`T_1 = \varepsilon_0`$ and $`T_{m+1} = \mathrm{st}(T_m)`$: $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1) = \sup_m T_m`$, the least fixed point of $`\mathrm{st}`$ (the referee checked it against the
  Lean definitions of the closure, one constructor at a time).
- **REGION$`^M`$, SHAPE$`^M`$, STAGE-TOWER** (proved). The label of a stage is a whole code of a lower module system. Inside the pair $`a \lt_2 b`$ of the pair block a copy of a smaller label lies below the
  point $`p`$ of the larger one, and $`p`$ is its carrier, so the gap problem of the stage codes goes away. The patterns are fan-free; a label inside the pair adds no link to a chain beyond its own,
  so a lower system of chain number $`k'`$ gives one of chain number $`\max(3, k'+1)`$ (with labels above $`b`$: $`k'+2`$).
- **LADDER** (proved). Natively, with $`\Theta_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$:

```math
\iota(\mathrm{CH}_k) \ge \mathrm{st}^{k-2}(\Theta_1)\ (k \ge 2),\qquad \iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1),\qquad \sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1).
```

  Before, $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$. The labels above $`b`$ alone give $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1)`$, a fallback if the placement inside the pair were rejected.
  So RED-TOWER covers every $`t \lt \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ natively, with a chain number that grows with $`t`$. Pair-free region codes past $`\varepsilon_0`$ are not needed.
- **Open**: labels $`\xi \ge \Omega_1`$ (the stage index then carries parameters, which the ordinal side does not handle yet; for such labels the native side is only an outline); labels $`\ge \Omega_\omega`$
  and the tower of $`\Omega`$'s; chain number 3 beyond $`\mathrm{st}(Z_\omega)`$. $`\theta_0`$ lies far above.
- The referee's other minor points: the paper uses one letter for two maps; its header claim that the native gap is gone holds only for coded labels; the bounds on record are lower bounds;
  one predicted comparison of two tops is not covered by the lemmas; one line on $`\psi_\pi(e) \gt \Omega_1`$ for $`\pi \gt \Omega_1`$ should be added.

### 1.4 Status after the twenty-seventh round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{22}]`$ given FRAG ($`[0, X_{21}]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$. No InaccPsi upper
  bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches: exact (given FRAG) for every short restart with $`\tau \lt G_2`$ and every long restart with code below $`G(\hat\zeta_3)`$ at level 1; with base change, for every code below $`\varepsilon_{\hat G+1}`$ at every level;
  CAP-0 for every code below $`G(\theta_4\cdot\omega^2)`$.
- Names: no change (every $`\upsilon`$-point below $`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ has the name $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$).
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on all 3,166 sample matrices (no change); natively $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1)`$,
  $`\sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ and $`\iota(\mathrm{CH}_2) \ge \Theta_1`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: LOW is not decided; $`u_4`$ is not self-crossing; the pin with moved atoms is repaired. Left: LOW$`^\infty`$, (R1″), (R2″), (R5).

### 1.5 Checks of the twenty-seventh round

Each run was under 60 seconds; none is a proof.

- §1.1. The rule data of PSI-θ$`^{(3)}`$; the rule against the order of the terms on 2 × 49,506 pairs, 0 mismatches (a deliberately wrong rule gives 67); the cushion margins on about 360 normal
  multipliers per seed, 0 failures; the ceiling at $`\theta_4\cdot\omega^2`$ on 1,067 samples; names, normal forms and the chain $`X_{21} \lt u_4 \lt X_{22}`$ in Python and Lean (green, identical). The referee: the rule
  with high parts up to $`\hat\zeta_G`$ on 16,512 pairs per seed (two seeds), 0 mismatches (a broken rule gives 18); the cushion near $`\theta_4\cdot\omega^2`$ on 125 multipliers and the next-element rule on 237, 0 failures; the
  test that refutes the proof of EX-RED; the Lean rerun is identical.
- §1.2. Orders, memberships, landing offsets, bounds and the tier over $`\hat G`$ (5 tests, 0 failures). The referee: the author's tests re-run with the same output; 15 of 15, 150 of 150 and 30 of 30
  own tests; a test that finds level-1 restarts with $`\pi_\eta \lt \hat G`$.
- §1.3. Names, memberships and a random test of FIX-σ, 0 failures; 34 label blocks are fan-free patterns with chain number 2 (inside) and 3 (above); Lean green. Certificates (replayed):
  forward 10 of 14, tops below $`\mathrm{CH}_k`$ 1 of 4, reverse 0 of 6 (nothing proved rests on them). The referee: the author's runs byte-identical, three certificates replayed, Lean green and identical;
  46,356 own terms, none above the predicted bound; own checker for the 34 blocks, 0 errors.

### 1.6 Open

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past $`G(\theta_4\cdot\omega^2)`$ and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{22}`$ given FRAG: exact landing reaches from the code $`G(\hat\zeta_3) + 1`$ on; the two-sided hull cap from $`G(\hat\zeta_A)`$ on, at $`\Omega_k`$ ($`k \ge 5`$) and at $`\Omega_\omega`$; EX-RED (its proof
  breaks at the last cushion term); the lower-bound side of the tiers above $`\Omega_3`$.
- The first inaccessible: stage labels $`\ge \Omega_1`$ (stage indices with parameters), labels $`\ge \Omega_\omega`$, chain number 3 beyond $`\mathrm{st}(Z_\omega)`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all
  standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\theta_4\cdot\omega^2), P')`$); LOW$`^\infty`$; (R1″), (R2″), (R5); then (D1b) and (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{22}`$; the rest of
  [COVER.md](COVER.md) §9.
