[← Back](README.md) | [English](SHIFT6.md) | [Japanese](SHIFT6-ja.md)

# $`R_2^+`$, the twenty-seventh to twenty-ninth rounds: exact long reaches, the cushion cap, the blocking point B-1 and its repair, the reduction EX-RED$`^w`$, the moved-lower pin, and native codes up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$

This page continues [SHIFT5.md](SHIFT5.md) (§2 there is the twenty-sixth round); §1 is the twenty-seventh round, §2 the twenty-eighth, §3 the twenty-ninth; the thirtieth to thirty-second rounds are on [SHIFT7.md](SHIFT7.md), the thirty-third and thirty-fourth on [SHIFT8.md](SHIFT8.md), the thirty-fifth to thirty-seventh on [SHIFT9.md](SHIFT9.md), the thirty-eighth on [SHIFT10.md](SHIFT10.md). The status words are those of [README.md](README.md) §3: **proved** means that
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

### 1.1 PSI-θ past the index $`\theta_2+1`$, exact long reaches below $`G(\hat\zeta_3)`$, and the cushion cap: $`\nu_C \ge X_{22}`$ given FRAG (not proved as written, §2.1; restored, §3.1)

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
  (The referee: the paper writes the bound of LAND-B with "$`+1`$", which is false as written; with "$`+\omega^2`$" every use holds.) **Second review** (§2.1): the stated exact value is false at some
  codes (blocking point B-1), so the exact value and MONO-L$`^{(3)}`$ are **not proved as written**; THETA$`^{(3)}`$ and LAND-B are not affected.
- **FAR-PIN$`^{L3}`$, OWN-PREFIX$`^f`$** (proved by transfer, given FRAG). Every code below $`G(\hat\zeta_3)`$ is an exact atom for the far pins. At $`\hat\zeta_f`$ the restart's own prefix of code $`\hat G + G_2`$ lands $`\Omega_1 + \omega^2`$
  further on, so READ$`^L`$ fails there by this prefix as well, and the hull cap CAP$`^\sharp`$ holds on that family. (The referee: the limit step at $`\hat\zeta_H`$ must be written out.) FAR-PIN$`^{L3}`$ is not proved at the codes of B-1 (§2.1).
- **CUSHION** (proved by transfer, given FRAG). A cap that needs no hull. Let $`\lambda`$ be a restart with code $`m`$ in $`[G(\zeta), G(\zeta+1))`$, $`G(\hat\zeta_3) \le m \lt G(\theta_4\cdot\omega^2)`$, and let $`C`$ be the sum of the
  terms of $`R_\lambda(\zeta)`$ with exponent $`\ge G_2`$, plus $`G_2`$. With the cap reading $`\Phi_\lambda`$ of [SHIFT2.md](SHIFT2.md) §2.1:

```math
r(\lambda) \lt H(\eta_\lambda + C + \omega^2\cdot\Phi_\lambda(m) + \omega^2).
```

  Every landing of a code below $`G(\hat\zeta_3)`$ lies less than $`G_2`$ beyond its own prefix, so the term $`G_2`$ absorbs every overshoot, and $`\omega^2\cdot\Phi_\lambda(m)`$ separates the codes.
  (The referee: the paper writes "$`+1`$" for "$`+\omega^2`$" here too; and in the arithmetic lemma "prefix" must be "proper prefix".) **Not proved as written** (§2.1): its pins use the
  exact atoms of B-1.
- **Corollaries** (proved by transfer, given FRAG). **CAP-0 for every code below $`G(\theta_4\cdot\omega^2)`$** (before: below $`G(\hat\zeta_H)`$): every multiplier in $`[\Omega_3, \Omega_4)`$, the plateau top $`u_4`$, and the multipliers in
  $`[\Omega_4, \theta_4\cdot\omega^2)`$. **$`u_4`$ is not self-crossing**, with no hypothesis, so case (ii) of DICHOTOMY-4″ never happens. LONG-CLASS$`^{22}`$: $`r(\lambda) \ge H(\eta_\lambda + G(\hat\zeta_3))`$ implies
  $`m_\lambda \ge G(\theta_4\cdot\omega^2)`$. LOW-RED$`^{22}`$: LOW$`_x`$ implies cofinally many self-crossing long restarts below $`x`$ with codes in $`[G(\theta_4\cdot\omega^2), P')`$. These rest on CUSHION, so they are **not proved
  as written** either (§2.1); CAP-0 below $`G(\hat\zeta_H)`$ stays proved.
- **Theorem X22** (proved, given FRAG, in the first review; the second review, §2.1, found the blocking point B-1 in its inputs, so it is **not proved as written**; restored with the repair of §3.1):

```math
\nu_C \ge X_{22} = \psi_{\Omega_1}(\Omega_\omega + \theta_4\cdot\omega^2 + \omega^{G(\theta_4\cdot\omega^2)+1}\cdot 2),\qquad G(\theta_4\cdot\omega^2) = \psi_{\Omega_2}(\Omega_\omega + \theta_4\cdot\omega^2).
```

From it the paper derived Wilken's claim in $`R_2^C`$ on $`[0, X_{22}]`$, both halves, given FRAG, and $`\nu_S \ge X_{22}`$ (both not proved as written now); also $`X_{21} \lt u_4 \lt X_{22}^- \lt X_{22}^\natural \lt X_{22} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (checked, Python and Lean).
With fewer of the new tools the same proof gives the fallbacks $`X_{22}^\natural`$ and $`X_{22}^-`$: $`\theta_4\cdot\omega^2`$ replaced by $`\Omega_4 + \psi_{\Omega_4}(\Omega_\omega + \Omega_4)`$ and by $`\Omega_4 + \theta_3`$. Also (P-LOW$`^{22}`$)
every restart $`a`$ with $`H(\theta_2\cdot\omega^2) \lt a \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ and (P) at $`(a, b)`$ has $`m_a \ge G(\theta_4\cdot\omega^2)`$. (The referee: one step should say that the region hypothesis of
CUSHION holds there.) **Conditional, not counted**: under not-LOW, $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\theta_4\cdot\omega^2)+1})`$.

- **Not proved** (blocking point; X22 does not use it; repaired as EX-RED$`^w`$ in §2.1): EX-RED, "exact atoms for every code below $`G(\Omega_k)`$ give CAP-0 below $`G(\Omega_{k+1})`$", and with it "not-LOW follows if every code below $`P'`$
  has an exact atom". The proof puts $`\omega^{G(\Omega_{k-1})+1}`$ in place of $`G_2`$; then the last term of the cushion has code $`G(\Omega_{k-1})+1`$, whose landing offset is uncountable ($`Z`$ for $`k = 4`$), so its atom
  lies above every possible target (the referee's test). The referee's possible repair (not checked): a stronger hypothesis "landing below $`R(\zeta) + \Omega_1`$" and a finite descending chain of
  cushion terms down to $`\omega^{Z+1}`$.
- **Open**: where the cushion stops. At $`\theta_4\cdot\omega^2`$ the reading is $`G(\hat\zeta_3)`$; up to $`\theta_4\cdot\omega^2 + \omega^{\psi_{\Omega_3}(\Omega_\omega + \theta_4\cdot\omega^2)+1}`$ the cushion extends in outline. The first code without a separating
  atom is $`G(\hat\zeta_3) + 1`$: there the landing cap gives only an upper bound, and the matching lower bound (EXACT-LAND) is open (now proved there, §2.1, §2.2). The two-sided hull cap from $`G(\hat\zeta_A)`$ on, at $`\Omega_k`$
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

Superseded by §2.4.


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

Superseded by §2.6.


- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past $`G(\theta_4\cdot\omega^2)`$ and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{22}`$ given FRAG: exact landing reaches from the code $`G(\hat\zeta_3) + 1`$ on; the two-sided hull cap from $`G(\hat\zeta_A)`$ on, at $`\Omega_k`$ ($`k \ge 5`$) and at $`\Omega_\omega`$; EX-RED (its proof
  breaks at the last cushion term); the lower-bound side of the tiers above $`\Omega_3`$.
- The first inaccessible: stage labels $`\ge \Omega_1`$ (stage indices with parameters), labels $`\ge \Omega_\omega`$, chain number 3 beyond $`\mathrm{st}(Z_\omega)`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all
  standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\theta_4\cdot\omega^2), P')`$); LOW$`^\infty`$; (R1″), (R2″), (R5); then (D1b) and (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{22}`$; the rest of
  [COVER.md](COVER.md) §9.

## 2. The twenty-eighth round

Three papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-seventh round proposed the repair (or checked the result) and a referee of this round checked it again. None of the papers uses Wilken, JSL 72 (2007),
Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this). Papers cited: [W07b] (L.2.1) in §2.1, checked by the referee against the paper; no paper is
used in a proved step of §2.2 or §2.3. No Lean file was added: the papers of §2.1 and §2.3 checked Lean files that only compare terms (`#eval`, no theorem; green, and identical in
the referees' reruns), so these count as checks; §2.2 has no Lean file. The minor points of the twenty-seventh-round reviews (§1) are applied: those of §1.1 by the paper of §2.1,
those of §1.2 by §2.2 and those of §1.3 by §2.3. Levels are numbered as in §1 (one higher than in the papers).

New names of this round:

```math
\hat g_4 = \psi_{\Omega_3}(\Omega_\omega + \theta_4\cdot\Omega_4),\qquad \hat\zeta_{23} = \theta_4\cdot\Omega_4 + \varepsilon_{\hat g_4+1},\qquad X_{23} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_{23} + \omega^{G(\hat\zeta_{23})+1}\cdot 2),
```

with $`R(\theta_4\cdot\Omega_4) = G(\hat\zeta_G)`$, $`R(\hat\zeta_{23}) = \varepsilon_{G(\hat\zeta_G)+1}`$, $`\theta_4\cdot\omega^2 \lt \theta_4\cdot\Omega_4 \lt \hat\zeta_{23} \lt \Omega_5`$ and
$`G(\hat\zeta_3) \lt G(\hat\zeta_3+\Omega_2) \lt G(\hat\zeta_G) \lt \varepsilon_{G(\hat\zeta_G)+1} \lt G(\hat\zeta_G+1) \lt G(\hat\zeta_A) \lt G(\hat\zeta_H)`$ (checked).
$`G(\hat\zeta_3+\Omega_2)`$ is the least fixed point of $`c \mapsto G(\hat\zeta_3 + c)`$ (checked by the referee of §2.2).

### 2.1 Exact landing reaches past $`G(\hat\zeta_3)+1`$, the repaired reduction EX-RED$`^w`$, and a blocking point against §1.1 (repaired, §3.1)

- **The minor points of the review of §1.1 are applied** (proved, **2 reviews**). The bound of LAND-B is $`r(\mu) \lt H(\eta_\mu + \Xi_\mu(D_\mu) + \omega^2) \le H(\eta_\mu + G_2)`$ and the
  cushion bound ends in $`+\omega^2`$, as every use needs; "prefix" is "proper prefix" in the cushion arithmetic; the step to $`\eta \ge \theta_2\cdot\zeta`$ has its line; the limit step of OWN-PREFIX$`^f`$
  at $`\hat\zeta_H`$ is written out, with constant-free multipliers below $`\hat\zeta_H`$ whose readings are cofinal in $`\omega^{\hat G+G_2}`$; the region hypothesis of CUSHION in Theorem X22 is checked;
  "proved (the obstruction)" is a remark. EX-RED of §1.1 is withdrawn.
- **Blocking point B-1 against §1.1** (found by the referee of this round, the second review of EXACT-LONG$`^{(3)}`$). The exact value of EXACT-LONG$`^{(3)}`$ ignores the code of the
  landing restart $`\nu^*`$. When a family starts with a landing restart whose code is short but at least $`\theta`$, then for $`m_0`$ between $`\theta`$ and that code times $`\omega`$ the stated
  value of the code $`G_2\cdot D + m_0`$ is below $`r(\nu^*)`$, while the same theorem's lower bound gives $`r(\lambda) \ge r(\nu^*)`$. Witness: the code $`G(\Omega_3) + \theta`$, whose landing
  restart has the code $`Z`$; one more witness lies in the range of this round. Such codes occur as exponents of cushions: the multiplier $`\Omega_4 + \omega^{\psi_{\Omega_3}(\Omega_\omega+\Omega_4)+\theta_2}`$ has the
  exponent $`G(\Omega_3) + \theta`$. So these are **not proved as written**: the exact value of EXACT-LONG$`^{(3)}`$, MONO-L$`^{(3)}`$, FAR-PIN$`^{L3}`$ at those codes, CUSHION, and with it
  Theorem X22, its fallbacks and the corollaries of CUSHION in §1.1 (CAP-0 from $`G(\hat\zeta_3)`$ to $`G(\theta_4\cdot\omega^2)`$, "$`u_4`$ is not self-crossing", LONG-CLASS$`^{22}`$, LOW-RED$`^{22}`$,
  P-LOW$`^{22}`$). Not affected: $`X_{21}`$ (its landings are at countable codes), every landing region, LAND-B and the other tail caps, CAP-0 below $`G(\hat\zeta_H)`$ ([SHIFT5.md](SHIFT5.md) §2.1),
  and the $`\varepsilon`$ tier below. The referee's evident repair (not checked): give the value with the code of $`\nu^*`$ added in front of $`m_0`$, then re-run the two directions and MONO.
- **THETA$`^{(3+)}`$** (proved by transfer). The native reading $`\Theta_\lambda`$ is defined on every code below $`G(\hat\zeta_G) = \psi_{\Omega_2}(\Omega_\omega + \theta_3\cdot\Omega_3)`$ (below $`\pi_\eta`$).
- **CROSS$`^L`$, LB$`^L`$** (proved by transfer, given FRAG). For every long code $`G_2\cdot D + m_0`$ with $`D`$ in $`[G(\hat\zeta_3), G(\hat\zeta_G))`$ the reach crosses the regions of the smaller
  codes and is at least the reach of its landing restart.
- **EXACT-LAND$`^A`$, MONO-L$`^A`$**: **false as stated** (B-1, the same pairs); the value holds where the landing restart has a code below $`\theta`$ or $`m_0 \lt \theta`$. Its first instances are
  proved: the code $`G(\hat\zeta_3)`$ reaches $`\delta_L + 1`$, the code $`G(\hat\zeta_3)+1`$ reaches $`\delta_L + 2`$, with $`L = H(\eta + G_2 + \omega^2)`$, and $`G(\hat\zeta_3) + G_2`$ lands at the offset
  $`G_2 + \omega^2\cdot 2`$ (there the landing restart has the long code $`G_2`$, so B-1 does not arise). FAR-PIN$`^{L,A}`$: proved except at the affected codes.
- **THETA$`^{e,G}`$, EXACT-LAND$`^F`$** (proved by transfer, given FRAG). The $`\varepsilon`$ tier of the family $`\hat G`$: every long code with $`D`$ in $`[G(\hat\zeta_G), \varepsilon_{G(\hat\zeta_G)+1})`$ has its exact
  reach, landing at $`H(\eta + \hat G + \Omega_1 + x_D)`$ with $`x_D`$ countable. Here the landing restart has the code $`\Omega_1`$ or a countable code, so B-1 does not arise. (The referee: one
  citation must be MULTI-RC$`^L`$ with the far pin, not MULTI-RC$`^U`$.)
- **NO-EX** (proved; (b) by transfer, given FRAG). The strengthening EX$`_{\mathrm{lit}}`$ that the twenty-seventh-round referee proposed, "a code in $`[G(\zeta), G(\zeta+1))`$ lands below
  $`R(\zeta) + \Omega_1`$", holds for every code below $`G(\hat\zeta_G)`$ and fails first at $`G(\hat\zeta_G)`$, where the landing is exactly $`R + \Omega_1`$. At $`G(\hat\zeta_G\cdot 2)`$ the landing is at least
  $`R + \Omega_1\cdot 2`$, so no bound $`R + \Omega_1\cdot n`$ works.
- **EX-RED$`^w`$** (proved by transfer, given FRAG; a reduction). EX$`^w`$ says: every long code $`c`$ has an exact or sharp atom whose landing offset is below $`\max(\Omega_1, R(\zeta_c)\cdot\omega)`$, where
  $`\zeta_c`$ is the multiplier of $`c`$. Then EX$`^w`$ below $`G(\Omega_k)`$ gives CAP-0 below $`G(\Omega_{k+1})`$, with a cushion that ends in the chain
  $`\omega^{G(\Omega_{k-1})+1} + \dots + \omega^{G(\Omega_3)+1} + \omega^{Z+1}`$ that the earlier referee proposed. Hence

```math
\text{not-LOW} \;\Leftarrow\; \text{CAP-0 below } P' \;\Leftarrow\; \mathrm{EX}^w \text{ for every code below } P'.
```

  This repairs the blocking point of EX-RED in §1.1. (The referee: EX$`^w`$ must bound the offset of sharp atoms too, or the sharp case must be part of the hypothesis; the pin along an
  uncountable landing offset is part of the hypothesis, not a transfer; one reading needs a definition when the quotient is below $`\theta`$; after B-1 the sharp option is not available for the
  affected codes.)
- **Not proved as written** (B-1): "EX$`^w`$ holds for every code below $`\varepsilon_{G(\hat\zeta_G)+1}`$"; CUSHION$`^\varepsilon`$, a second cushion $`R_{\mathrm{hi}} + \omega^{\hat G+1} + \omega^{\Omega_1+1}`$ that would give
  CAP-0 for every code below $`G(\hat\zeta_{23})`$; and with it $`\nu_C \ge X_{23}`$, Wilken's claim on $`[0, X_{23}]`$, the fallback with $`\theta_4\cdot\Omega_4`$ in place of $`\hat\zeta_{23}`$, and the bound under
  not-LOW. The referee found a cushion multiplier below $`\theta_4\cdot\Omega_4`$ with an affected exponent, and expects these to hold after the repair of B-1 (not checked). The arithmetic of
  CUSHION$`^\varepsilon`$ is proved and checked. $`X_{22} \lt X_{23} \lt H(\Omega_5)`$ (checked). All of this is restored with the repair of §3.1.
- **Open**: EX$`^w`$ past $`\varepsilon_{G(\hat\zeta_G)+1}`$ (the rest of the family $`\hat G`$ needs PSI-θ at the high part $`\Omega_\omega + \hat\zeta_G`$, only an outline; from $`G(\hat\zeta_A)`$ on, the
  two-sided hull cap). LOW: open.

### 2.2 $`\nu_C = \nu_S`$: the residue of REDUCTION$`^{(4)}`$

- **The minor points of the review of §1.2 are applied** (proved, **2 reviews**). The moved set is closed under Cantor normal form terms and exponents; the condition on the base is stated
  and holds at every use; PIN$`^{(2)}`$ is restated with the hypothesis on the atoms and on their hereditary parameters, and Lemma SIM shows that the same MULTI-RC induction supplies this
  hypothesis, so the callers need none; THETA$`^e`$ maps onto an initial segment only (onto all of $`[F_\lambda, \varepsilon_{F_\lambda+1})`$ when $`\pi_\eta \ge \varepsilon_{\hat G+1}`$); the inspection has its row for PUSH.
  So the results of §1.2 that needed PIN$`^{(2)}`$ without restriction hold under LOW$`^\infty`$, given FRAG (still **conditional, not counted**).
- **THETA$`^{(3+)}`$, EXACT-LAND$`^{G_2}`$** (proved by transfer, given FRAG). For every long code with $`D`$ in the family $`[G(\hat\zeta_3), G(\hat\zeta_3+\Omega_2))`$ the reach is exact and commutes
  with base change; the landing restart is $`H(\eta + G_2 + \omega^2\cdot(1+t))`$ with $`t`$ countable, read off $`\Theta_\lambda(D)`$. The code $`G(\hat\zeta_3)+1`$ reaches $`\delta_L + 2`$, the same value as in §2.1,
  found independently. Here the landing restart has the long code $`G_2`$, so B-1 does not arise. This is the separating atom that §1.1 named as missing at $`G(\hat\zeta_3)+1`$. (The referee: for a
  restart with $`\tau \ge \Omega_2`$ the code $`\pi_\eta`$ lies outside the domain, so $`\Theta_\lambda(\pi_\eta)`$ must be defined as the supremum, and the tails with such codes need one comparison.)
- **Results that rest on §1.1** (its referee found them proved, but they use EXACT-LONG$`^{(3)}`$ and CUSHION, against which §2.1 found B-1, so they are **not counted** until B-1 is repaired):
  HULL at every level; the pins along uncountable landing offsets (FAR-PIN$`^{L4}`$, MRC$`^{\mathrm{mv}}`$, LPIN$`^{\mathrm{mv}}`$); TC⁺, READ-EQ and MONO-F for every code below $`G(\hat\zeta_3+\Omega_2)`$; the caps (R2″)
  from CUSHION; the zone moved to $`H(\eta_x + G(\hat\zeta_3+\Omega_2))`$; and REDUCTION$`^{(5)}`$: $`\nu_C = \nu_S`$ follows from FRAG, LOW$`^\infty`$ and three open items, (R1‴) exact landing reaches for
  the codes from $`G(\hat\zeta_3+\Omega_2)`$ to $`\Omega_2`$ (and the restarts with $`\tau \ge \Omega_2`$ at levels $`\ge 2`$ inside blocks with offset $`\ge \Omega_2`$), (R2‴) caps for codes $`\ge G(\theta_4\cdot\omega^2)`$, (R5′)
  the zone past $`H(\eta_x + G(\theta_4\cdot\omega^2))`$. The restarts with $`\tau \ge \Omega_2`$ at level 1 (TAU-W2) are covered after the fix of the domain. The conditional zone up to
  $`H(\eta_x + G(\theta_4\cdot\omega^2))`$ is **not proved as stated** (its hypothesis is weaker than its proof uses).
- So the counted reduction is still REDUCTION$`^{(4)}`$ of §1.2. $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$ are both **open**.
- The referee's other minor points: "$`G_2\cdot D = D`$ on the family" is false (only the range of $`D`$ is right); one consistency remark needs $`\Theta \le \Phi`$ on the family (not used);
  one residue split leaves out (R2‴) for large offsets (the headline keeps it); the facts on $`G(\hat\zeta_3+\Omega_2)`$ are checked in Python only.

### 2.3 Native codes: stage labels of level $`\Omega_1`$ give no gain

- **The minor points of the review of §1.3 are applied** (**2 reviews**).
- **CONT$`^{\lim}`$** (proved): $`\psi_\kappa`$ is continuous at every limit argument (the referee checked it against the Lean definitions of the closure, one constructor at a time).
- **FIX-σ$`_l`$, SUP-1, SUP-D** (proved). For $`l \ge 2`$, $`\psi_{\Omega_l}(\Omega_\omega\cdot\Omega_l)`$ is the least fixed point of $`T \mapsto \psi_{\Omega_l}(\Omega_\omega\cdot T)`$ above $`\Omega_{l-1}`$;
  $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_l)`$ is the supremum of $`\psi_{\Omega_1}(\Omega_\omega\cdot S_m)`$ over the iterates $`S_m`$ of that map; $`\psi_{\Omega_1}(\Omega_\omega^2) = \sup_l \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_l)`$;
  and $`H(\eta)`$ is continuous at every limit $`\eta`$ of the domain.
- **LABEL-PAR, LIM$`^K`$, PRIM-T1$`^{\mathrm{vis}}`$, PUSH$`^S`$** (proved) and **STAGE$`^{\sigma 2}`$, CNST$`^T`$ with parameters** (proved by transfer). An uncountable stage set forces the labels to
  carry parameters; with them the stage systems of [SHIFT3.md](SHIFT3.md) §1.2–§1.3 hold for every stage below $`\psi_{\Omega_2}(\Omega_\omega\cdot\Omega_2)`$, and the native point of a realized stage set
  $`[1, S]`$ is at least $`\psi_{\Omega_1}(\Omega_\omega\cdot S)`$ for every $`S`$ in $`[\Omega_1, \psi_{\Omega_2}(\Omega_\omega\cdot\Omega_2))`$ with $`\Omega_\omega\cdot S`$ in the domain. So the ordinal side is ready for stage labels of level $`\Omega_1`$.
- **LABEL-OCC, LAM-LABEL, SIGMA-BARRIER** (proved, for label-block systems: the code shape of §1.3, with the labels compared below the point). If such a system has a stage of
  level $`\Omega_1`$, every countable $`T`$ below its limit $`Z`$ is a label, and each label adds one link to a chain, so the labels alone give

```math
\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1) \lt Z \le \iota(\mathrm{CH}_{k-1}).
```

  So such labels give **no gain**: a label-block system is never the first native bound past $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$. The paper's word "impossible" is overstated (the referee):
  it is not shown that such systems do not exist, and labels from another source past that point would still give a bound.
- **No new native bound.** The bounds of §1.3 stay. The case of non-initial label sets is only an outline. Conditional, not counted: a native family for the stages $`S_m`$ of level $`\Omega_1`$ (all $`m`$) would give
  $`\sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$.
- **Open**: a native system past $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ outside this class: labels without pairs compared another way, labels nested inside the pair of the code, labels
  as parameters, or systems without labels; labels of level $`\Omega_2`$ and up (they need a new rule for the items of the stage index); labels $`\ge \Omega_\omega`$.
- The referee's other minor points: the citation of the strictness needs one line on how the iterates are generated; that line also gives the domain condition for every $`m`$; one set of
  maximal subterms is stated a little wrongly and one top case is not written out; part of one chain of inequalities is only checked; the statement of SIGMA-BARRIER should fix $`Z`$.

### 2.4 Status after the twenty-eighth round

Superseded by §3.4.


- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{21}]`$ given FRAG (2 reviews); $`X_{22}`$ (§1.1) and $`X_{23}`$ (§2.1) are not proved as written (B-1).
  The core half holds on $`[0, \nu_C]`$. No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches (given FRAG): exact for every short restart with $`\tau \lt G_2`$ and every long restart with $`D \le \hat G`$ (2 reviews); for $`D`$ below $`G(\hat\zeta_3)`$ the stated exact value is false at some codes
  (B-1); exact on the family $`[G(\hat\zeta_3), G(\hat\zeta_3+\Omega_2))`$ and on the $`\varepsilon`$ tier $`[G(\hat\zeta_G), \varepsilon_{G(\hat\zeta_G)+1})`$ (1 review each). Base change: for every code below $`\varepsilon_{\hat G+1}`$
  at every level. CAP-0 for every code below $`G(\hat\zeta_H)`$.
- LOW: not decided. Not-LOW follows from EX$`^w`$ for every code below $`P'`$ (new reduction).
- Names: no change. The lower-bound program below $`\theta_0`$: no change; no new native bound, and label-block systems with labels of level $`\Omega_1`$ give no gain.
- $`\nu_C = \nu_S`$: open; left LOW$`^\infty`$, (R1″), (R2″), (R5); the finer residue of §2.2 waits for the repair of B-1.

### 2.5 Checks of the twenty-eighth round

Each run was under 60 seconds; none is a proof.

- §2.1. Five tests in 20 runs, 0 failures (orders and readings, the landings of the families, the cushion margins, the limit sequence at $`\hat\zeta_H`$, the frontier names); Lean green, identical
  to Python. The referee: own tests of the witnesses of B-1 (normal multipliers whose readings end in a short code $`\ge \theta`$), of CUSHION$`^\varepsilon`$ on about 130 multipliers per seed (two seeds) and
  8,778 and 8,646 ordered pairs, of the plateau data used by EX-RED$`^w`$, and of two cushion multipliers with an affected exponent; no ordinal check failed; the Lean rerun is identical.
- §2.2. Six tests: orders and readings all true, 738 of 738 family landings, 13 of 13 zone bases, 624 of 624 zone landings, the ceiling witnesses all true, 13 of 13 zone tops. The referee: 280 of
  280 family landings with larger $`t`$ (a first run with an unsorted sample gave 40 false failures; the sorted rerun counts), the fixed point $`G(\hat\zeta_3+\Omega_2)`$, restarts with the code $`\pi_\eta`$; the Lean
  file of §1.1 rechecked, green.
- §2.3. 97 checks per seed, two seeds, 0 failures (424 of 750 random terms lie above the previous rung); Lean green and identical. The referee: byte-identical reruns, Lean green and identical,
  about 32,000 own random tests at levels 2 and 3, 0 failures.

### 2.6 Open

Superseded by §3.6.


- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs caps past $`G(\hat\zeta_H)`$ and a lower bound at the code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{21}`$ given FRAG: repair B-1 (exact long reaches with the code of the landing restart), then CUSHION ($`X_{22}`$) and CUSHION$`^\varepsilon`$ ($`X_{23}`$); EX$`^w`$ past
  $`\varepsilon_{G(\hat\zeta_G)+1}`$; the two-sided hull cap from $`G(\hat\zeta_A)`$ on, at $`\Omega_k`$ ($`k \ge 5`$) and at $`\Omega_\omega`$; the lower-bound side of the tiers above $`\Omega_3`$.
- The first inaccessible: a native system past $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ outside the label-block systems; labels of level $`\ge \Omega_2`$ and $`\ge \Omega_\omega`$; chain number 3 beyond
  $`\mathrm{st}(Z_\omega)`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (EX$`^w`$ for every code below $`P'`$ would refute it); LOW$`^\infty`$; (R1″), (R2″), (R5); then (D1b) and (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{21}`$; the rest of
  [COVER.md](COVER.md) §9.

## 3. The twenty-ninth round

Three papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-eighth round proposed the repair (or checked the result) and a referee of this round checked it again, or that the papers of §3.1 and §3.2 prove it
independently and both referees found it proved. None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees
checked this). Papers cited: [W07b] (L.2.1) in §3.1 and §3.2, checked by both referees against the paper; no paper is used in a proved step of §3.3, which does not
use FRAG. No Lean file was added: the paper of §3.2 checked a Lean file that only compares terms (`#eval`, no theorem; green, and identical in the referee's rerun),
the referee of §3.1 rechecked the Lean files of §1.1 and §2.1 (green, identical), and the referee of §3.3 checked the ordinal inputs with such a file (green, identical
to Python); these count as checks. The minor points of the twenty-eighth-round reviews are applied: those of §2.1 by the paper of §3.1 and those of §2.3 by §3.3
(**2 reviews**); of those of §2.2, the paper of §3.2 uses the value at the codes $`\pi_\eta`$ (the supremum of the smaller values). Levels are numbered as in §1 (one
higher than in the papers).

New names of this round. For a restart $`\nu`$ and a short code $`c`$ in its domain, $`\mathrm{cl}_\nu(c)`$ is the reach that EXACT-CL\* gives to a restart of code $`c`$ in the
region of $`\nu`$ (so $`r(\nu) = \mathrm{cl}_\nu(\tau_\nu)`$ when $`\tau_\nu \lt G_2`$). For a long code $`G_2\cdot D + m_0`$ with landing restart $`\nu^*`$, the **landing code** $`\tau^*`$ is the code of $`\nu^*`$,
plus $`m'_0`$ when the last exponent of the family base is a long code $`G_2\cdot D' + m'_0`$ (then $`\nu^*`$ is the landing restart of that exponent). Also, with $`S_1 = \Omega_1`$ and
$`S_{m+1} = \psi_{\Omega_2}(\Omega_\omega\cdot S_m)`$ (§2.3):

```math
L(1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'),\qquad \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1) \lt \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2) = \sup_m \psi_{\Omega_1}(\Omega_\omega\cdot S_m).
```

### 3.1 The repair of B-1: $`X_{22}`$ and $`X_{23}`$ restored, given FRAG

- **The minor points of the review of §2.1 are applied** (proved, **2 reviews**). The step "$`\le`$" of EXACT-LAND$`^F`$ cites MULTI-RC$`^L`$ with the far pin; EX$`^w`$ allows exact atoms only, so
  the sharp case is not needed; $`l(c) = 0`$ when the quotient is below $`\theta`$; the far pin along an uncountable landing offset is a stated hypothesis of EX-RED$`^w`$.
- **MONO-cl, AGREE, EQ-cl** (proved; the paper calls the first and the last MONO-F and EQ-F, renamed here because MONO-F names another lemma in §1.2). $`c \mapsto \mathrm{cl}_\nu(c)`$ is
  strictly increasing, its values are closed points of the region of $`\nu`$, cofinal in it, and it commutes with the transports. For every short $`\tau_\nu`$ and every $`x \lt \theta`$:

```math
\mathrm{cl}_\nu(\tau_\nu + x) = r(\nu) + \Theta_\nu(x).
```

  So the old value of EXACT-LONG$`^{(3)}`$ and the corrected one differ exactly on the class of B-1: family starts whose last exponent $`a_n`$ is a short code $`\ge \theta`$, with
  $`m_0 \in [\theta, a_n\cdot\omega)`$. The referee proved this description of the class from the reading ($`D = G(\zeta)`$ with $`R(\zeta)`$ a multiple of $`\Omega_1`$ whose last exponent lies in
  $`[\theta, G_2)`$). (The referee: one step of EQ-cl argues about the domain wrongly; the claim holds because the code is a sum of parts that are in the domain.)
- **EXACT-LONG$`^{(3)\sharp}`$, MONO-L$`^{(3)\sharp}`$, FAR-PIN$`^{L3\sharp}`$** (proved by transfer, given FRAG). For every long code $`G_2\cdot D + m_0`$ with $`D \lt G(\hat\zeta_3)`$:

```math
r(\lambda) = \mathrm{cl}_{\nu^*}(\tau^* + m_0).
```

  It is strictly increasing in the code, at least $`r(\nu^*)`$, and equal to the old value outside the class of B-1. The witness $`G(\Omega_3) + \theta`$ now reaches $`\mathrm{cl}_{\nu^*}(Z + \theta) \gt r(\nu^*)`$.
  Every code below $`G(\hat\zeta_3)`$ is an exact atom for the far pins, and all this holds at every level. The value has **2 reviews**: the paper of §3.2 derives the same formula
  independently, and its referee found it proved on this range. (The referee's remark: for every $`m_0 \lt G(\omega+1)`$ the value is $`r(\nu^*) + \Theta_{\nu^*}(m_0)`$.)
- **EXACT-LAND$`^{A\sharp}`$, MONO-L$`^{A\sharp}`$, FAR-PIN$`^{L,A\sharp}`$, EX below $`\varepsilon_{G(\hat\zeta_G)+1}`$** (proved by transfer, given FRAG). The same formula for $`D`$ in $`[G(\hat\zeta_3), G(\hat\zeta_G))`$; EXACT-LAND$`^F`$
  of §2.1 is unchanged. So every code below $`\varepsilon_{G(\hat\zeta_G)+1}`$ has an exact reach that commutes with the transports and increases strictly with the code, and is an exact atom (no
  sharp atom is used).
- **Restored** (proved by transfer, given FRAG; 1 review of the repair, while the rest of each proof had the review of §1.1 or §2.1): CUSHION, CAP-0 for every code below
  $`G(\theta_4\cdot\omega^2)`$, "$`u_4`$ is not self-crossing", LONG-CLASS$`^{22}`$, LOW-RED$`^{22}`$, P-LOW$`^{22}`$; CUSHION$`^\varepsilon`$, CAP-0 for every code below $`G(\hat\zeta_{23})`$, LONG-CLASS$`^{23}`$, LOW-RED$`^{23}`$. The two
  cushion witnesses of §2.1 are checked. Hence, given FRAG,

```math
\nu_C \ge X_{22},\qquad \nu_C \ge X_{23} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_{23} + \omega^{G(\hat\zeta_{23})+1}\cdot 2),
```

  and $`\nu_S \ge X_{23}`$, the fallbacks $`X_{22}^\natural`$, $`X_{22}^-`$, $`X_{23}^-`$, and **Wilken's claim in $`R_2^C`$ on $`[0, X_{23}]`$, both halves, given FRAG** (the core half by
  $`[0, X_{23}] \subseteq [0, \nu_C]`$, the names half because $`X_{23}`$ is a normal form, Lemma L). Conditional, not counted: the bounds under not-LOW.
- **The results of §2.2 that rest on §1.1**: HULL at every level and the pins along uncountable landing offsets (FAR-PIN$`^{L4}`$, MRC$`^{\mathrm{mv}}`$, LPIN$`^{\mathrm{mv}}`$) for the codes below
  $`G(\hat\zeta_3+\Omega_2)`$ now hold (proved by transfer, given FRAG). **Not proved as asserted**: TC⁺ and READ-EQ at the codes of B-1 (they need EQ-cl for base changes, not only for
  transports; the paper has one sentence). So REDUCTION$`^{(5)}`$ of §2.2 is still not counted.
- The referee's other minor points: the names (above), and "the first code without EX$`^w`$" means "the first code where EX$`^w`$ is not proved"; the additivity of $`\Theta_\nu`$ comes
  from the counting rule PSI-n, not from the reading; one instance and one exponent are named slightly wrongly.

### 3.2 PSI-θ at every high part, the native reading below $`P'`$, and an attempt at not-LOW (blocking point b1)

- **PSI-θ$`^k`$, PSI-W$`^{(k)}`$, PSI-W, NEXT** (proved by transfer, checked). For every $`k \ge 3`$ the counting rule for $`\psi_{\Omega_j}`$ ($`2 \le j \lt k`$) holds for every normal form
  $`\psi_{\Omega_j}(\Omega_\omega + \zeta_H + \delta)`$ with $`\zeta_H`$ a multiple of $`\Omega_{j+1}`$ below $`\theta_k\cdot\Omega_k`$ ($`\theta_k = \psi_{\Omega_{k+1}}(\Omega_\omega)`$) and $`\delta \lt \Omega_{j+1}`$, by a downward
  induction on $`j`$ from the rule at the unit $`\Omega_k`$. So the rule holds for every normal form $`\psi_{\Omega_2}(\beta)`$ with $`\beta \lt \Omega_\omega\cdot 2`$, and for every normal multiplier
  $`\zeta \lt \Omega_\omega`$, $`G(\zeta+1)`$ is the next element of the class of the rule after $`G(\zeta)`$. This is the PSI-θ at the high part $`\Omega_\omega + \hat\zeta_G`$ that §2.1 lacked.
  (The referee: the checks test only the order that the rule predicts, not the constants or the forms.)
- **THETA$`^\omega`$** (proved by transfer). The native reading $`\Theta_\lambda`$ is defined on every code below $`\pi_{\eta_\lambda}`$, so on all codes below $`P'`$, with the supremum of the smaller values at
  $`\pi_\eta`$. (The referee: one stated value applies $`\Theta`$ to an ordinal that is not a code; read the shifted reading there.)
- **HULL-ARITH** (proved). A calculus of landings: a family start lands at the larger of two sources, the supremum of the earlier landings (with a shift when they overshoot)
  and the reaches of its own prefixes; the landing offset of a code $`c`$ is below $`\omega^{l(c)+1} \le \omega^c`$, where $`l(c)`$ is the leading exponent of the reading of its multiplier.
- **LAND$`^\omega`$**: the crossing and the lower bounds (CROSS, LB, EXACT "$`\ge`$") are proved by transfer, given FRAG; so every long code below $`P'`$ reaches at least
  $`\mathrm{cl}_{\nu^*}(\tau^* + m_0)`$. **Not proved** (blocking point b1, found by the referee): the upper bound "$`\le`$" and the pin (PIN). They need a far pin through landings that
  have long exponents themselves, at every depth, relative to a copy at the outer restart, where only $`h \ge T`$ is known on the moved lower parameters, and so on the hereditary
  parameters of the atoms (as in Lemma SIM of §2.2). This is refereed only for short landings (codes below $`G(\hat\zeta_3)`$, §1.1) and for $`D \lt G(\hat\zeta_3+\Omega_2)`$ (§2.2); the paper
  asserts it as "(PIN) by induction", without the relative form. Witnesses: the code $`G(\Omega_5)`$, whose own source of code $`G(\Omega_4)`$ lands at $`G(\Omega_3) + Z`$, and the code
  $`G(\theta_4\cdot\omega^2)`$. For codes without constants the gap may close; it is real for codes with constants read by $`\Theta`$, which are the codes that LOW-RED produces.
- So these are **not proved**: MONO-L$`^\omega`$, FAR-PIN$`^{L,\omega}`$, LONG-CLASS$`^\omega`$, EX$`^w`$ past $`\varepsilon_{G(\hat\zeta_G)+1}`$ (at $`\Omega_3`$, at $`\Omega_4`$ and at every $`\Omega_k`$), CAP-0 below $`P'`$,
  **not-LOW** ($`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$), $`\nu_C \ge L(1)`$, and the claim on $`[0, L(1)]`$. The reductions themselves are correct (from CAP-0 below $`P'`$ to not-LOW, the region
  hypothesis, the bootstrap with MULTI-FAR$`_k`$). **LOW stays undecided.**
- The referee's other minor points: the paper states CAP-1 for codes in $`[P', P'_1)`$, but CAP-1 is about the codes below $`P'`$ at level 2; if the transfer to level 2 used for
  $`\nu_C \ge L(1)`$ held, the known reduction would give more than $`L(1)`$, so the text must reconcile the two; one bound is written with $`\cdot 2`$ for $`\cdot(c+1)`$; one agreement is with a
  refereed cap, not with an exact value; the new cases of the transfer are only sketched.

### 3.3 Native codes: labels as points inside the pair of the code, and $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$

Words of §1.3 and §2.3.

- **The minor points of the review of §2.3 are applied** (**2 reviews**): "impossible" is "no gain"; the line that generates the $`S_m`$, which gives the domain condition for every $`m`$; the
  remark on label sets that are not initial is an outline; the part of a chain of inequalities that is only checked is labelled so; $`Z`$ is fixed in SIGMA-BARRIER.
- **LABEL-IN-K, SHAPE$`^q`$** (proved). Labels carry their parameters, so every stage label $`T`$ of a code is a parameter of the code, and the code of $`T`$ already lies in the row of
  level $`\Omega_1`$ inside the pair $`(x, y)`$ of the code. A pair block no longer holds a copy of the label; it points to the point $`q(T)`$ of that code by the reach of its left end:

```math
g \lt a \lt_2 b,\qquad a \le_1 b + q(T),\qquad g \le_1 b + g + V_j(\beta).
```

  The labels lie below $`y`$, so they never extend the chains from $`x`$, and every code and top is a fan-free pattern with chain number at most 2, also when the labels are codes of
  the system itself. So the barrier of §2.3 does not apply.
- **PAIR-DOWN** (proved; one step of Carlson's rule R1, whose hypotheses the referee matched with Carlson 2009, Lemma 5.5 and Def 5.3). To copy a block with a smaller label
  $`T' \lt T`$, first reflect the pair at its own left end $`a`$, then the head. This removes the gap of the copy rule ([SHIFT3.md](SHIFT3.md) §1.2, open item), and one top, a single pair
  with $`a \le_1 b\cdot 2`$ (a pattern of 10 elements), serves every stage set.
- **TOP-MAKE$`^q`$, ROW$`^q`$, TOP-HOST$`^q`$** (proved), **ATOM-HOST-N$`^q`$, HOST-Γ, LEVEL-HOST, NEST-HOST** (proved by transfer). (The referee: TOP-HOST$`^q`$ holds when "a code over $`X`$" means
  that $`X`$ carries the parameters of the hosted code, including the module chains of large labels, as in the earlier definition; with parameters read as bare points it is false.
  "It does not depend on $`S`$" means that the configuration does not; the parameters do.)
- **IDX$`^q`$** (proved). For every stage $`S`$ below $`\psi_{\Omega_2}(\Omega_\omega\cdot\Omega_2)`$ these codes form a module system with chain number 3, so natively

```math
\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot S)\ \ (\Omega_\omega\cdot S \text{ in the domain}),\qquad \iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2).
```

  This supersedes LADDER of §1.3: already $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$. **RED-TOWER holds with the one chain number 3** for every $`t \lt \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$ (before:
  below $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$, with a growing chain number). Already the point of the top for the argument 0 is at least $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$, so the remark of
  [SHIFT3.md](SHIFT3.md) §1.2 that index systems below $`\Omega_2`$ stay below $`\upsilon^*`$ is superseded: these systems go far past $`\upsilon^*`$. These are lower bounds only; no upper bound for that point or for
  $`\iota(\mathrm{CH}_3)`$ is known. (The referee tried a counterexample to TOP-HOST$`^q`$ with a label whose module is the top itself; it fails, since the module chain of such a label is a
  parameter below the code.)
- **Outline, open**: labels of level $`\Omega_l`$, $`l \ge 2`$ (native side only an outline, ordinal side open; given both, $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega^2)`$, conditional, not counted);
  labels $`\ge \Omega_\omega`$, $`\Omega_{\omega+1}`$, $`\Omega_{\omega\cdot 2}`$, and on to $`\theta_0`$.
- The referee's other minor points: TOP-HOST$`^q`$ (above); the number of roots of rule R3 is not defined and two indices are mixed up; the new certificates belong in the record (§3.5).

### 3.4 Status after the twenty-ninth round

Superseded by [SHIFT10.md](SHIFT10.md) §1.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{23}]`$ given FRAG ($`[0, X_{21}]`$ with 2 reviews; $`X_{22}`$ and $`X_{23}`$ with 1 review of the repair, §3.1).
  The core half holds on $`[0, \nu_C]`$. No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches (given FRAG): exact for every short restart with $`\tau \lt G_2`$ and every long restart with code below $`G(\hat\zeta_3)`$ (2 reviews), and with code below $`\varepsilon_{G(\hat\zeta_G)+1}`$ (1 review);
  for every code below $`P'`$ the lower bound $`\mathrm{cl}_{\nu^*}(\tau^* + m_0)`$. Base change: for every code below $`\varepsilon_{\hat G+1}`$ at every level. CAP-0 for every code below $`G(\hat\zeta_{23})`$.
- LOW: not decided. Not-LOW follows from EX$`^w`$ for every code below $`P'`$; EX$`^w`$ holds below $`\varepsilon_{G(\hat\zeta_G)+1}`$, and the attempt past it stops at b1.
- Names: no change. The lower-bound program below $`\theta_0`$: natively $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$, RED-TOWER with chain number 3 below it; the step below SRO: no change.
- $`\nu_C = \nu_S`$: open; left LOW$`^\infty`$, (R1″), (R2″), (R5); REDUCTION$`^{(5)}`$ waits for TC⁺ at the codes of B-1.

### 3.5 Checks of the twenty-ninth round

Each run was under 60 seconds; none is a proof.

- §3.1. 9 of 9 witnesses of B-1: the new values start at the reach of the landing restart, increase, and equal the old ones when $`m_0 \ge a_n\cdot\omega`$; the two cushion witnesses; 299
  sampled multipliers, 105 of them in the class of B-1, 0 failures (new: when $`a_n = \theta`$ the old value at $`m_0 = \theta`$ equals $`r(\nu^*)`$, so the old MONO fails there too). The referee: the reruns
  are identical; new seeds 3 and 4 give 55 and 51 family starts of the class, 0 failures; the algebra of AGREE in an abstract model, 1,440 tests, 0 failures; the Lean files of §1.1 and §2.1 green and
  identical.
- §3.2. The rule against the order of the terms past $`\hat\zeta_G`$, for $`\psi_{\Omega_3}`$, and with high parts up to $`\Omega_5`$ (2 × 37,442, 2 × 35,156 and 2 × 15,750 ordered pairs), 0 mismatches; one deliberately
  wrong rule is detected, three others are not detected by this order test. The calculus on 795 multipliers in $`[\Omega_2, \Omega_6)`$: the named values with a refereed value or bound agree,
  and the monotonicity, the bound, the absorption and NEXT have 0 failures; Lean green, identical to Python. The referee: a new seed (400 multipliers, 41,594 pairs), own tests of the
  instances of LONG-CLASS$`^\omega`$ near $`\theta_{k+1}\cdot\omega^2`$ ($`k = 2, 3, 4`$, two seeds) and of the bound at depth 2 (248 and 240 exponents), all 0 failures; the Lean rerun is identical.
- §3.3. 15 new codes and tops (4 with labels that are codes of the system) are fan-free patterns with chain number 2. Certificates (replayed): forward 11 of 19 (among them a block with a
  label of level 3 below the label-free top, and that top below $`\mathrm{CH}_3`$), the other 8 timed out at 45 seconds; reverse 0 of 5. The referee: byte-identical rerun; labels nested 4 deep
  (up to 301 nodes) give patterns with chain number 2, and with the labels moved above $`y`$ the chain number is 3, so the test can tell them apart; 3 of 6 new forward certificates, all for
  the new copy rule (a smaller label with a larger argument); 0 of 7 predicted-false; $`\mathrm{CH}_2`$ below the top, so the top lies between $`\mathrm{CH}_2`$ and $`\mathrm{CH}_3`$; the ordinal inputs
  for $`m = 1, \dots, 7`$, 0 failures, Lean green and identical to Python.

### 3.6 Open

Superseded by [SHIFT10.md](SHIFT10.md) §1.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs caps past $`G(\hat\zeta_{23})`$ and a lower bound at the code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The claim above $`X_{23}`$ given FRAG: the relative pin of b1 (far pins through long landings at every depth, with $`h \ge T`$ on the hereditary parameters), then the upper bound of
  LAND$`^\omega`$ (it contains the two-sided hull cap), EX$`^w`$ past $`\varepsilon_{G(\hat\zeta_G)+1}`$ and CAP-0 below $`P'`$; the lower-bound side of the tiers above $`\Omega_3`$.
- The first inaccessible: labels of level $`\Omega_l`$ ($`l \ge 2`$), on the ordinal side and the native side; labels $`\ge \Omega_\omega`$, $`\Omega_{\omega+1}`$, $`\Omega_{\omega\cdot 2}`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$;
  the step for all standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (not-LOW follows from EX$`^w`$ below $`P'`$, which waits for b1); LOW$`^\infty`$; (R1″), (R2″), (R5); TC⁺ at the codes of B-1; then (D1b) and (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{23}`$; the rest of
  [COVER.md](COVER.md) §9.
