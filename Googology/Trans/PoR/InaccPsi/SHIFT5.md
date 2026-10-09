[← Back](README.md) | [English](SHIFT5.md) | [Japanese](SHIFT5-ja.md)

# $`R_2^+`$, the twenty-fifth and twenty-sixth rounds: $`\nu_C \ge X_{21}`$ given FRAG, the landing cap and the hull cap, exact long reaches up to the first index fixed point, TC⁺ at every level, GEN for every η, and native codes up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$

This page continues [SHIFT4.md](SHIFT4.md) (§2 there is the twenty-fourth round); §1 is the twenty-fifth round and §2 the twenty-sixth; the twenty-seventh round is on [SHIFT6.md](SHIFT6.md). The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

## 1. The twenty-fifth round

Three papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-fourth round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. Papers cited here: [W07a]
(L.3.30, L.4.7) and [W07b] (L.2.1, Thm 2.2, Def 4.1, the proof of Thm 5.3), as in [SHIFT4.md](SHIFT4.md) §1. No Lean file was added: two papers (§1.1, §1.3) checked a Lean file
that only compares terms (`#eval`, no theorem; green, and green in the referees' reruns), and the referee of §1.2 wrote one of the same kind (green), so these count as checks.
The minor points of the twenty-fourth-round reviews are applied: those of [SHIFT4.md](SHIFT4.md) §2.1 and §2.2 by the paper of §1.1 (checked again by its referee, **2 reviews**),
the label point of §2.4 there by §1.3, and the rest in [SHIFT4.md](SHIFT4.md) §2. Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher than in the papers):
level 1 is below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$.

Notation of [SHIFT4.md](SHIFT4.md): $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$, $`G_2 = G(\omega^2)`$, $`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$,
$`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$, the reading $`R`$ of §2.2 there, and $`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$. New names of this round (with $`\hat\zeta_2`$ of [SHIFT4.md](SHIFT4.md) §2.2):

```math
\hat\zeta_3 = \theta_3\cdot\omega^2,\quad g_3 = \psi_{\Omega_3}(\Omega_\omega + \hat\zeta_3),\quad \varepsilon_+ = \varepsilon_{G_2+1},\quad \hat\zeta_4 = \hat\zeta_3 + \omega^{\omega^{g_3\cdot 2}},\quad \hat\zeta_\varepsilon = \hat\zeta_3 + \varepsilon_{g_3+1},
```

with $`R(\hat\zeta_3) = G_2`$, $`R(\hat\zeta_4) = \omega^{G_2^2}`$, $`R(\hat\zeta_\varepsilon) = \varepsilon_+`$, and $`\hat\zeta_2 \lt \hat\zeta_3 \lt \hat\zeta_4 \lt \hat\zeta_\varepsilon \lt \Omega_4`$ (checked).

### 1.1 The landing cap: $`\nu_C \ge X_{19}`$ given FRAG

- **The minor points of the twenty-fourth-round reviews of [SHIFT4.md](SHIFT4.md) §2.1 and §2.2 are applied** (proved, **2 reviews**). Among them: the false step of the proof of $`X_{18}`$
  is replaced by a lemma on least multiples (the least multiple of $`\omega^e`$ above $`\gamma`$ is $`\ge \gamma + \omega^{e'}`$ for $`e' \le e`$); D-UNC$`^{\mathrm{SEG}}`$ for bases $`\eta \ge \Omega_2\cdot a`$ (the case that was used and not stated);
  the successor step of the reading derived from the counting rule PSI-n; the tail bases above $`H(\Omega_3)`$; the non-separation at $`\tau_{\mathrm{LH}}`$ is only a remark (below). So the proofs of
  $`X_{17}`$ and $`X_{18}`$, with these repairs, have **2 reviews** (the referee of §1.2 also redid the last step of the proof of $`X_{18}`$).
- **CROSS-SHARP$`^{(3)\prime}`$** (proved by transfer, given FRAG). For constant-free normal $`M \in [\Omega_3, \hat\zeta_3]`$: $`m_\lambda \ge G(M)`$ implies $`r(\lambda) \ge H(\eta_\lambda + R(M))`$; the converse holds for
  $`M \in [\Omega_3, \hat\zeta_\varepsilon]`$ with $`R(M)`$ a multiple of $`\Omega_1`$. This is the sharp form of [SHIFT4.md](SHIFT4.md) §2.2, restricted as its referee asked. (The referee: add one line that the
  realizer induction does not depend on the level.)
- **SEP$`^{\mathrm{near}}`$** (proved, given FRAG). Every code $`c \lt G_2`$ has a separating pin, whose atom is the reach given by EXACT-CL\*. So the pin at the exponent $`\tau_{\mathrm{LH}} + 1`$, missing in
  [SHIFT4.md](SHIFT4.md) §2.2, exists: the reaches at $`\tau_{\mathrm{LH}}`$ and $`\tau_{\mathrm{LH}} + 1`$ are $`\varphi(\omega, \delta+1)\cdot\omega`$ and $`\varphi(\omega, \delta+1)\cdot\omega + 1`$.
- **The cap below $`G(\hat\zeta_3)`$** (proved by transfer, given FRAG). Every restart $`\lambda`$ below $`\min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ with $`G(\Omega_3+1) \le m_\lambda \lt G(\hat\zeta_3)`$ has $`r(\lambda) \lt H(\eta_\lambda + \Xi_\lambda + \omega^2)`$,
  with the cap offset $`\Xi_\lambda`$ of the reading and the block index chosen above the block of the last pin atom. So CAP-0 holds below $`G(\hat\zeta_3)`$. (The referee: the paper calls this the literal
  cap of READ, but the fine form of that cap, with the least block index $`\ge 2`$, is already false below $`\hat\zeta_3`$, at $`M = \theta_3\cdot(\omega\cdot 2+1)`$; what is proved is the coarse cap above.
  No result depends on the fine form.)
- **NO-LIT, LAND-LB** (proved, given FRAG). At $`\hat\zeta_3`$ the cap with its target in the region of the last prefix restart is **false**: $`\lambda = H(\hat\zeta_3)`$ has the code $`G(\hat\zeta_3)`$ and
  $`r(\lambda) \ge r(H(\hat\zeta_3 + G_2)) \ge H(\hat\zeta_3 + G_2 + \omega^2)`$. In general, a restart that reaches a long restart $`\nu`$ reaches $`r(\nu)`$, which lies past the region of $`\nu`$. This is the blocking point of
  [SHIFT4.md](SHIFT4.md) §2.2 (no separation in the needed form above $`G_2`$) in exact form.
- **THETA⁺, EXACT-LONG⁺** (proved by transfer, given FRAG). For a long restart $`\lambda`$ with the code $`G_2\cdot D + m_0`$, $`D \lt \varepsilon_+`$, $`m_0 \lt G_2`$, the reach is exact: it lands at the index distance
  $`\omega^2\cdot\Theta^+(D)`$, where $`\Theta^+`$ is an order isomorphism of the codes below $`\varepsilon_+`$ that commutes with transports. Before, exact long reaches were known for $`D \lt G_2`$.
- **FAR-PIN$`^L`$, MULTI-RC$`^L`$, TOP-REG-LAND** (proved by transfer, given FRAG). A long prefix restart is pinned through its atom in its landing region (a nested pin); with this, the rule TOP-REG
  holds with its target in the landing region of the last long prefix restart, above every pin atom. (The referee: say in one sentence that the condition on the pattern points of the old rule changes.)
- **LAND-CAP** (proved by transfer, given FRAG). Every restart $`\lambda`$ below $`\min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ with $`G(\Omega_3+1) \le m_\lambda \lt G(\hat\zeta_\varepsilon)`$ has $`r(\lambda) \lt H(\eta_\lambda + \Xi^*_\lambda + \omega^2)`$, where
  the landing offset $`\Xi^*_\lambda`$ is the cap offset with the landing distance of the last long prefix restart added (equal to $`\Xi_\lambda`$ below $`G(\hat\zeta_3)`$). Corollaries: **CAP-0 for every code below
  $`G(\hat\zeta_\varepsilon)`$**; EXACT-G($`\hat\zeta_3`$): a restart with code $`G(\hat\zeta_3)`$ has $`r(\lambda) = r(H(\eta_\lambda + G_2)) = \delta_L + 1`$ with $`L = H(\eta_\lambda + G_2 + \omega^2)`$; LONG-CLASS$`^{19}`$ ($`r(\lambda) \ge H(\eta_\lambda + \varepsilon_+)`$
  implies $`m_\lambda \ge G(\hat\zeta_\varepsilon)`$); LOW-RED$`^{19}`$: LOW$`_x`$ implies cofinally many self-crossing long restarts with codes in $`[G(\hat\zeta_\varepsilon), P')`$ below $`x`$.
- **DICHOTOMY-4′** (proved, given FRAG, under the hypothesis $`H(\Omega_4 + G(\Omega_3) + Z + \omega^2) \le \nu_S`$). For $`u_4 = H(\Omega_4)`$: either CAP-0 holds at $`u_4`$, or cofinally many restarts below $`u_4`$ with
  codes in $`[G(\hat\zeta_\varepsilon), G(\Omega_4))`$ reach $`H(\eta + G(\Omega_3))`$. Also $`r(u_4) \gt H(\Omega_4 + G_2 + \omega^2)`$. This repairs the dichotomy of [SHIFT4.md](SHIFT4.md) §2.2 (not proved there).
  (The referee: the range of the second case rests on EXACT-LONG⁺; without it the range is $`[G(\hat\zeta_4), G(\Omega_4))`$.)
- **Theorem X19** (proved, given FRAG):

```math
\nu_C \ge X_{19} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_\varepsilon + \omega^{G(\hat\zeta_\varepsilon)+1}\cdot 2),\qquad G(\hat\zeta_\varepsilon) = \psi_{\Omega_2}(\Omega_\omega + \hat\zeta_\varepsilon).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{19}]`$, both halves, given FRAG**, $`\nu_S \ge X_{19}`$, and $`X_{18} \lt H(\hat\zeta_3) \lt X_{19} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (checked, Python and Lean).
Also (P-LOW$`^{19}`$) every restart $`a`$ with $`H(\theta_2\cdot\omega^2) \lt a \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ and (P) at $`(a, b)`$ has $`m_a \ge G(\hat\zeta_\varepsilon)`$. Without EXACT-LONG⁺ (but with the other lemmas of this section) the same
proof gives $`\nu_C \ge X_{19}^- = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_4 + \omega^{G(\hat\zeta_4)+1}\cdot 2)`$. **Conditional, not counted**: under not-LOW, $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\hat\zeta_\varepsilon)+1})`$.

- **Not proved** (open): the landing cap at every normal multiplier below $`\Omega_\omega`$ (conjecture READ$`^L`$; it would give CAP-0 for every code below $`P'`$, hence not-LOW; it is false, §2.1); exact long reaches for
  $`D \ge \varepsilon_+`$ (outline: the same proof through the base changes of [SHIFT2.md](SHIFT2.md) §1.1, up to codes $`G(\Omega_1)`$); past $`G(\Omega_1)`$ the realizer reading and the cap reading differ, and no
  general separation is known; LOW; (P); (Q′).
- The referee's other minor points: the fallback cites the wrong check (it needs that every exponent on $`[\hat\zeta_3, \hat\zeta_4)`$ is below $`G_2^2`$; the referee's test shows it); one output labels
  a point "X19" that is not $`X_{19}`$; the ceiling at $`\hat\zeta_\varepsilon`$ should cite the referee's test; one case ($`D = 0`$) of the crossing lemma of EXACT-LONG⁺ must be defined on its own.

### 1.2 $`\nu_C = \nu_S`$: TC⁺ below $`G_2^2`$ and the spans below $`\omega^{G_2^2}`$

Notation of [SHIFT3.md](SHIFT3.md) §1.4 and §2.4 (TC⁺, LOW, LOW$`^\omega`$, (D1b), (E4)); $`\pi_\eta = \psi_{\Omega_2}(\Omega_\omega + \theta\cdot\eta)`$. Every proved result of this subsection is at level 1.

- **D-UNC$`^\pi`$** (proved, no FRAG). For $`\eta \in D`$ and a normal form $`\xi \lt \pi_\eta`$: $`\eta + \xi \in D`$ iff the constants of $`\xi`$ are below $`H(\eta + \xi)`$; summands of $`\eta`$ may be absorbed.
  (The referee: D-UNC$`^Z`$ of [SHIFT4.md](SHIFT4.md) §1.4 is not a case of it, contrary to the paper; at $`\eta = 1, 2, \omega^2`$ the offset $`\xi = \pi_\eta \lt Z`$ gives $`\eta + \xi \in D`$, which D-UNC$`^\pi`$ does not cover.)
- **BC$`^\pi`$** (proved at level 1, no FRAG). The η-base changes are defined on all offsets below a constant-free bound $`\Gamma \le \pi_\beta`$, with absorption at the target allowed; in the setting of
  $`\nu_C = \nu_S`$ every base is above $`H(\hat\zeta_2)`$, so $`\Gamma = G(\hat\zeta_2)`$ works.
- **READ-EQ** (proved). A base change commutes with the reading $`\Theta`$ on codes below $`G_2`$. This settles a minor point of the review of [SHIFT3.md](SHIFT3.md) §1.4.
- **TC⁺ below $`G_2^2`$, MONO-F** (proved, given FRAG, at level 1). A base change $`B`$ keeps reaches, $`r(BR) = B(r(R))`$, for every short restart with $`\tau \lt G_2`$, every long restart with code
  $`G_2\cdot D + m_0`$, $`D, m_0 \lt G_2`$, and at the code $`G(\Omega_3)`$; so the code transport holds for every such base change. The exact reach is strictly increasing in the code below $`G_2^2`$. (The referee:
  both halves need FRAG; the paper's "the half ≤ needs no FRAG" is wrong.) Past $`G_2^2`$ only brackets are known.
- **The cap below $`G(\hat\zeta_3)`$ again** (proved by transfer, given FRAG): the same route as §1.1 gives CAP-0 below $`G(\hat\zeta_3)`$ and $`\nu_C \ge X_{\hat\zeta_3} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_3 + \omega^{G(\hat\zeta_3)+1}\cdot 2)`$, a point below $`X_{19}`$.
  **Not proved**: the matching bound under not-LOW (it needs these caps at level 2). (The referee: normality of the multiplier is essential; a non-normal $`\zeta \lt \hat\zeta_3`$ can have $`R(\zeta) \ge G_2`$.)
- **Conditional, not counted** (correct under LOW, given FRAG; the paper claims them under LOW$`^\omega`$). For every (D1b) span whose η-offset is below $`\omega^{G_2^2}`$: the bookkeeping past every index fixed point,
  room below $`G(\hat\zeta_3)`$, pins at exponents below $`G_2^2`$ with a far TOP-REG, and TC⁺ at every recorded restart (U0–U3); so these spans are placed (PLACE$`^{T2}`$, RES-ALL$`^{T2}`$), and
  $`c_u = H(\eta_u + \omega^{G_2^2})`$ is a zone system (ZONE$`^{(2)}`$). **Blocking point**: LOW$`^\omega`$ adds only the case $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, which the conjectured names predict, and there these
  steps need the level-2 forms of the exact long reaches, of CROSS-O and the pins, of the cap below $`G(\hat\zeta_3)`$, of LONG-CLASS and of BC$`^\pi`$, none of which is proved. So the blocking point of the
  review of [SHIFT3.md](SHIFT3.md) §1.4 (everything there under LOW) still stands.
- **The residue** (the paper's assembly, with LOW for LOW$`^\omega`$ and one outline step). $`\nu_C = \nu_S`$ would follow from: exact reaches that commute with base change for long codes $`\ge G_2^2`$;
  caps for codes $`\ge G(\hat\zeta_3)`$ (room); the inspection after TWIST (outline); and LOW. §1.1 gives exact long reaches for $`D \lt \varepsilon_+`$ and caps below $`G(\hat\zeta_\varepsilon)`$, but no paper shows that they
  commute with base change. $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$ are both **open**.
- The referee's other minor points: one citation in the pins (the region transport, not READ-EQ); one place uses the dictionary that the paper says it does not use; the first open case has
  code $`G_2^2 + 1`$, not $`G_2^2`$.

### 1.3 GEN for every η, and native codes up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$

Write $`D_\infty`$ for the class of all ordinals $`\eta`$ with $`\eta \in \mathrm{Cl}(\Omega_\omega + \theta\cdot\eta, H(\eta))`$, $`\iota(\eta)`$ for the order type of $`D_\infty \cap \eta`$, and $`\upsilon^\infty = \sup H[D_\infty]`$.

- **EXTRACT$`^\infty`$, NFD$`^\infty`$** (proved). For $`\eta \ge \Omega_\omega\cdot\omega`$ the summand $`\Omega_\omega`$ is absorbed into $`\theta\cdot\eta`$, but the terms $`\omega^{\theta+a_i}`$ are still Cantor normal form summands, so $`\eta`$
  is read back as before; the absorbed $`\Omega_\omega`$ was never used. So the obstruction of [SHIFT4.md](SHIFT4.md) §2.4 (the extraction step of GEN-EXT past $`\Omega_\omega\cdot\omega`$) is not one.
- **Theorem GEN-ALL** (proved; the referee re-read the proofs of STEP and LOW-STEP line by line: neither puts a bound on the argument $`A`$). For every $`\eta \in D_\infty`$:

```math
H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) = \upsilon_{1+\iota(\eta)}.
```

GEN, GEN-EXT and GEN⁺ are restrictions of GEN-ALL, so the label question of [SHIFT4.md](SHIFT4.md) §2.4 is settled. $`I_\omega \in D_\infty`$ and $`\Omega_\omega + \theta\cdot I_\omega = I_\omega`$, so
$`\psi_{\Omega_1}(I_\omega)`$, the reading A of the core ([README.md](README.md) §2), is itself a $`\upsilon`$-point, and $`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$.

- **The bases $`\Omega_\omega\cdot\xi`$** (proved; the base tools by transfer, the η-form tools by transfer at inventory level). For every $`\xi \ge 1`$ with $`\Omega_\omega\cdot\xi \in D_\infty`$, the point $`\psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$ is
  a restart with code $`P_\xi = \psi_{\Omega_2}(\Omega_\omega\cdot(1+\xi))`$; D-UNC holds for offsets below $`\pi_\eta`$; the base changes, the fixed points, the dictionary, the split and the code transport hold at
  level $`1+\xi`$.
- **PUSH$`^{\omega^\omega}`$** (proved; chain length 3; the derivation **2 reviews**, as the conditional result of [SHIFT4.md](SHIFT4.md) §2.4, now with GEN-ALL for its condition). Natively

```math
\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega).
```

The strict $`\gt`$ would need a remark of [SHIFT3.md](SHIFT3.md) §1.2 that is not proved.

- **The names half** (proved). Every $`\upsilon`$-point below $`\upsilon^\infty`$ (so every restart, block start and index fixed point there) has the exact name $`H(\eta)`$, $`\eta \in D_\infty`$; below $`\psi_{\Omega_1}(I_\omega)`$
  its collapse arguments are below $`I_\omega`$. **REL-ETA** (proved by transfer) for every long restart below $`\upsilon^\infty`$. (The referee: the paper's header says LOW$`^\omega`$ is no longer needed, but it is
  replaced by $`\nu_C \lt \upsilon^\infty`$, which is open.)
- **Theorem X$`^{(1+\xi)}`$** (proved, given FRAG; for every $`\xi \ge 1`$ with $`\Omega_\omega\cdot\xi \in D_\infty`$): $`\nu_C`$ is not in $`(\psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi)), Y_\xi)`$ with $`Y_\xi = \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi) + \omega^{\mathbb{G}^\vartheta+1})`$
  ($`\mathbb{G}^\vartheta`$ of [SHIFT3.md](SHIFT3.md) §1.1; without FRAG with $`G_2`$ for $`\mathbb{G}^\vartheta`$). $`\xi = 1`$ is X$`^{(2)}`$ of [SHIFT3.md](SHIFT3.md) §2.4. **Conditional, not counted**: if $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$,
  then the claim holds in $`R_2^C`$ on $`[0, Y_\xi]`$; proved for $`\xi \lt I_\omega`$. **Not proved** for $`\xi \ge I_\omega`$ (blocking point; the paper stated it for every $`\xi`$): $`\psi_{\Omega_1}(I_\omega)`$ has only the normal
  form with argument $`I_\omega`$, so $`[0, Y_\xi]`$ is not inside reading A, and there $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$ would refute reading A.
- **Open**: LOW, CAP-0, CAP-1 and their analogues at level $`1+\xi`$; the reaches of restarts with $`\tau \ge \Omega_2`$ at levels $`\ge 2`$; (P). Natively: $`\mathrm{CH}_2`$ past $`\Theta_1`$ (no change);
  stages $`\ge \omega^\omega`$ (they need chain number 4, so they bound $`\iota(\mathrm{CH}_4)`$) and uncountable stage indices. The ordinal side no longer limits a native bound of the form $`\psi_{\Omega_1}(\Omega_\omega\cdot T)`$.
- The referee's other minor points: $`\theta\cdot\Omega_1 = \Omega_1`$ is false (harmless; the same slip is in the paper of [SHIFT4.md](SHIFT4.md) §2.4); one constant set leaves out $`\{1\}`$ (harmless);
  the paper never tested countable levels or offsets in $`[P_\xi, \pi_\eta)`$ (the referee did); one step is an application of the η-form tools at lower levels, not an induction.

### 1.4 Status after the twenty-fifth round

The twenty-sixth and twenty-seventh rounds changed this status; see §2.4 and [SHIFT6.md](SHIFT6.md) §1.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{19}]`$ given FRAG ($`[0, X_{18}]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$. No InaccPsi upper
  bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches: exact (given FRAG) for every short restart with $`\tau \lt G_2`$ and every long restart with $`D \lt \varepsilon_+`$; caps for every code below $`G(\hat\zeta_\varepsilon)`$.
- Names: every $`\upsilon`$-point below $`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ has the name $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on all 3,166 sample matrices (no change); natively $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$ and
  $`\iota(\mathrm{CH}_2) \ge \Theta_1`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: LOW is not decided; CAP-0 holds for every code below $`G(\hat\zeta_\varepsilon)`$ (given FRAG); TC⁺ holds below $`G_2^2`$ at level 1. Left: (P1), (D1b), (E4).

### 1.5 Checks of the twenty-fifth round

Each run was under 60 seconds; none is a proof.

- §1.1. Names, normal forms, readings and the order chain $`X_{17} \lt X_{18} \lt \dots \lt X_{19}^- \lt X_{19} \lt H(\Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ in Python and Lean (green); the exponents of 3,000 normal multipliers,
  the margin, the order on 861,202 pairs, D-UNC on 2,400 landing offsets, the ceiling and the least-multiple lemma: 0 failures. The referee: the witness against the fine cap; the ceiling at
  $`\hat\zeta_\varepsilon`$ on 611 samples; the exponents near $`\hat\zeta_4`$ and $`\hat\zeta_\varepsilon`$ (30,338 pairs); D-UNC on 1,572 offsets; the margin on 198,787 pairs: 0 failures; the Lean rerun and an own Lean file are green.
- §1.2. The tier bounds, $`R(\hat\zeta_3) = G_2`$, 1,039 multipliers, D-UNC$`^\pi`$ on 4,423 offsets (1,532 with absorption), the atom substitution on 388 codes: 0 failures (Python only). The referee: 238 normal
  multipliers, D-UNC$`^\pi`$ on 1,219 offsets at bases of level 3: 0 failures; a Lean file of the order chains, green.
- §1.3. The maps $`B`$ of STEP and $`E`$ of LOW-STEP with 15 arguments $`A`$ from $`\Omega_\omega\cdot\omega`$ up to $`I_\omega + \theta`$ (about 6 million pairs), the normal-form test on 1,620 values at 9 levels, D-UNC on 2,016 tests,
  the codes on 429 samples: 0 failures; three broken variants of $`E`$ fail. Lean green. The referee: extraction on other hulls (8,012 tests), strict increase of $`H`$ and $`\pi`$ (25,440 pairs), D-UNC with
  offsets in $`[P_\xi, \pi_\eta)`$ (792 tests), $`B`$ and $`E`$ with countable atoms in $`A`$ (about 600,000 pairs): 0 failures; the Lean rerun is identical.

### 1.6 Open

The twenty-sixth and twenty-seventh rounds changed this list; the current list is [SHIFT6.md](SHIFT6.md) §1.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past $`G(\hat\zeta_\varepsilon)`$ and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{19}`$ given FRAG: exact long reaches for $`D \ge \varepsilon_+`$ (outline up to $`G(\Omega_1)`$); a separation past $`G(\Omega_1)`$; the landing cap at every $`\Omega_k`$ (READ$`^L`$, now false, §2.1);
  the lower-bound side of the tiers above $`\Omega_3`$.
- The first inaccessible: native stages $`\ge \omega^\omega`$, uncountable stage indices, $`\Omega_{\omega+1}`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\hat\zeta_\varepsilon), P')`$), LOW$`^\omega`$ (now: the level-2 forms of the tools of §1.2), TC⁺ for long codes $`\ge G_2^2`$, caps for codes $`\ge G(\hat\zeta_3)`$ in the
  placement, (D1b), (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{19}`$; the rest of
  [COVER.md](COVER.md) §9.

## 2. The twenty-sixth round

Three papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-fifth round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. Papers cited: [W07b] (L.2.1, Thm 2.2,
the proof of Thm 5.3) in §2.1; no paper is used in a proved step of §2.2 or §2.3 (§2.3 quotes Carlson 2001 in a remark only, and does not use FRAG). No Lean file
was added: each paper checked a Lean file that only compares terms (`#eval`, no theorem; green, and green in the referees' reruns), so these count as checks.
The minor points of the twenty-fifth-round reviews are applied: those of §1.1 by the paper of §2.1 and those of §1.2 by the paper of §2.2, and their
referees checked them again (**2 reviews**, except one line, see §2.2); the rest are recorded in §1. Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher
than in the papers): level 1 is below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, and level $`1+\xi`$ holds the restarts $`H(\Omega_\omega\cdot\xi + \eta')`$ with $`0 \lt \eta' \lt \Omega_\omega`$.

Names of §1 and of [SHIFT2.md](SHIFT2.md) §1 and §2.1: $`\Phi' = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\omega^2 + \Omega_2)`$, $`\hat G = G(\Omega_2)`$ (the least fixed point of $`G`$), and, for a restart $`\lambda`$,
$`F_\lambda = H(\eta_\lambda + \Omega_1)`$, its first index fixed point. New names of this round (the multipliers carry a hat, as $`\hat\zeta_3`$ does):

```math
\hat g_3 = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot\Omega_3),\quad \hat\zeta_G = \theta_3\cdot\Omega_3,\quad \hat\zeta_A = \hat\zeta_G + \Omega_2,\quad \hat\zeta_H = \hat\zeta_G + \omega^{\hat g_3+g_3},\quad \hat\zeta_f = \hat\zeta_H + \Omega_2,
```

with $`R(\hat\zeta_G) = \hat G`$, $`R(\hat\zeta_A) = \hat G + \Omega_1`$, $`R(\hat\zeta_H) = \omega^{\hat G+G_2}`$, $`R(\hat\zeta_f) = \omega^{\hat G+G_2} + \Omega_1`$, and $`\hat\zeta_\varepsilon \lt \hat\zeta_G \lt \hat\zeta_A \lt \hat\zeta_H \lt \hat\zeta_f \lt \Omega_4`$ (checked).

### 2.1 Exact long reaches up to the first index fixed point; READ$`^L`$ is false; the hull cap: $`\nu_C \ge X_{21}`$ given FRAG

- **The minor points of the review of §1.1 are applied** (proved, **2 reviews**). The cap proved below $`G(\hat\zeta_3)`$ is now called the coarse cap, and NO-LIT is a statement
  about the coarse cap only (the fine form, with the least block index $`\ge 2`$, is false below $`\hat\zeta_3`$, at $`\theta_3\cdot(\omega\cdot 2+1)`$). The ceiling at $`\hat\zeta_\varepsilon`$ is proved by the
  one-line argument of the reading, with the test as evidence. The case $`D = 0`$ of the crossing lemma of EXACT-LONG⁺ is defined as the value that EXACT-CL\* gives. The fallback of
  §1.1 is "without EXACT-LONG⁺" and cites the right test; the range of DICHOTOMY-4′ is stated with and without EXACT-LONG⁺.
- **THETA$`^V`$, EXACT-LONG$`^V`$** (THETA$`^V`$ proved; EXACT-LONG$`^V`$ proved by transfer, given FRAG). On the Veblen and Γ tier over $`G_2`$ a reading $`\Theta^V`$ maps the codes
  below $`\Phi'`$ onto an initial segment and commutes with the transports. So a long restart with code $`G_2\cdot D + m_0`$, $`D \lt \Phi'`$, has an exact reach.
- **THETA$`^G`$** (proved). The counting rule PSI-θ ([SHIFT3.md](SHIFT3.md) §2.1) holds at every multiplier below $`\hat G`$. With it, a native order-type reading $`\Theta_\lambda`$
  is defined on all codes below $`\hat G`$: it reads a code in $`[G(\zeta), G(\zeta+1))`$ at the moved base $`\upsilon_{\lambda+1+\Theta_\lambda(\zeta)}`$. It maps these codes onto $`[0, F_\lambda)`$
  and commutes with the transports. The realizer reading and the cap reading of [SHIFT2.md](SHIFT2.md) §2.1, which differ past $`G(\Omega_1)`$, lie below and above it.
  (The referee: one step, "the supremum is at most $`F_\lambda`$", is argued wrongly; it holds by an induction the referee gives. Two citations must be added: the forms at
  uncountable multipliers need PSI-n with a high part, and the covering lemma of the codes; the paper should state that the reading stays in the hull. Applied in the twenty-seventh round, [SHIFT6.md](SHIFT6.md) §1.1.)
- **EXACT-LONG$`^G`$, EXACT-F** (proved by transfer, given FRAG). A long restart $`\lambda`$ with code $`G_2\cdot D + m_0`$, $`m_0 \lt G_2`$, has its exact reach for every $`D \lt \hat G`$:
  it lands at the index distance $`\omega^2\cdot\Theta_\lambda(D)`$, below $`F_\lambda`$. For $`D = \hat G`$ it lands at $`F_\lambda`$ itself: $`r(\lambda) = r(F) + \Theta_F(m_0)`$ for the restart $`F = H(\eta_\lambda + \Omega_1)`$
  (for $`m_0 \lt \theta`$). So the exact long reaches now reach the first index fixed point. Before, they were known for $`D \lt \varepsilon_+`$. (The referee: cite the rule TOP-REG-LAND of §1.1
  for the targets, not the far rule TOP-REG-FAR, which covers only targets below $`\delta_j\cdot\omega`$.)
- **LAND-CAP past $`\hat\zeta_\varepsilon`$** (proved by transfer, given FRAG). The landing cap of §1.1 holds for every code in $`[G(\Omega_3+1), G(\hat\zeta_A))`$, the family $`\hat G`$
  (codes in $`[G(\hat\zeta_G), G(\hat\zeta_A))`$) included; and the sharp crossing CROSS-SHARP$`^{(3)\prime\prime}`$ holds up to $`\hat\zeta_G`$. EXACT-G($`\hat\zeta_G`$): a restart with code $`G(\hat\zeta_G)`$ reaches
  exactly as far as the restart $`H(\eta_\lambda + \hat G + \Omega_1)`$.
- **NO-READL** (proved by transfer, given FRAG; it rests on EXACT-LONG$`^G`$ and EXACT-F, which are new). The conjecture READ$`^L`$ of §1.1 (the landing cap at every normal multiplier) is
  **false**. It holds for every code below $`G(\hat\zeta_A)`$, and it fails at every restart with code
  $`G(\hat\zeta_A) = \psi_{\Omega_2}(\Omega_\omega + \theta_3\cdot\Omega_3 + \theta_2\cdot\Omega_2)`$. Witness: $`\lambda = H(\theta_2\cdot\hat\zeta_A) = \psi_{\Omega_1}(\Omega_\omega + \theta_3\cdot\Omega_3 + \theta_2\cdot\Omega_2)`$. READ$`^L`$ says
  $`r(\lambda) \lt H(\eta_\lambda + \hat G + \Omega_1 + \omega^2)`$, but $`r(\lambda) \ge H(\eta_\lambda + \hat G + \Omega_1 + \omega^2)`$. The points used lie below $`X_{20} \le \nu_S`$ (below), so no extra hypothesis is
  needed. Cause: the codes of the family $`\hat G`$ land at the index fixed point and then move on by a countable amount, past the point where the next family starts.
  (The referee: say that the value of the cap does not depend on how one reads the remark on "the maximum of the landings".)
- **CAP$`^\sharp`$, READ$`^\sharp`$ below $`G(\hat\zeta_H)`$** (proved by transfer, given FRAG). The hull cap: on a family whose reading is $`X + \Omega_1`$ with $`X`$ ending in a long code of quotient
  $`\hat G`$, the cap offset is shifted by $`F'' = H(\eta_\lambda + X + \Omega_1)`$. With this shift the cap holds for every code in $`[G(\Omega_3+1), G(\hat\zeta_H))`$. Corollaries: **CAP-0 for
  every code below $`G(\hat\zeta_H)`$**; LONG-CLASS$`^{21}`$ ($`r(\lambda) \ge H(\eta_\lambda + \omega^{\hat G+G_2})`$ implies $`m_\lambda \ge G(\hat\zeta_H)`$); LOW-RED$`^{21}`$: LOW$`_x`$ implies cofinally many self-crossing
  long restarts with codes in $`[G(\hat\zeta_H), P')`$ below $`x`$. At $`G(\hat\zeta_A)`$ the reach lies in $`[H(\eta + \hat G + \Omega_1 + \omega^2), H(\eta + \hat G + \Omega_1 + F'' + \omega^2))`$; its exact value is open.
- **DICHOTOMY-4″** (proved, given FRAG, under the hypothesis of DICHOTOMY-4′). Either CAP-0 holds at $`u_4 = H(\Omega_4)`$, or cofinally many restarts below $`u_4`$ with codes in
  $`[G(\hat\zeta_H), G(\Omega_4))`$ reach $`H(\eta + G(\Omega_3))`$. So READ$`^L`$ at the plateau top $`G(\Omega_4)`$ itself is not refuted; NO-READL refutes its general form.
- **Theorem X21** (proved, given FRAG):

```math
\nu_C \ge X_{21} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_H + \omega^{G(\hat\zeta_H)+1}\cdot 2),\qquad G(\hat\zeta_H) = \psi_{\Omega_2}(\Omega_\omega + \hat\zeta_H).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{21}]`$, both halves, given FRAG**, $`\nu_S \ge X_{21}`$, and $`X_{19} \lt X_{20} \lt X_{21} \lt H(\Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (checked, Python and Lean).
Also (P-LOW$`^{21}`$) every restart $`a`$ with $`H(\theta_2\cdot\omega^2) \lt a \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ and (P) at $`(a, b)`$ has $`m_a \ge G(\hat\zeta_H)`$. Without CAP$`^\sharp`$ the same proof gives
$`\nu_C \ge X_{20} = \psi_{\Omega_1}(\Omega_\omega + \theta_2\cdot\hat\zeta_A + \omega^{G(\hat\zeta_A)+1}\cdot 2)`$, and with fewer of the new tools three smaller points between $`X_{19}`$ and $`X_{20}`$. (The referee: the ceiling at
$`\hat\zeta_A`$ is proved, not only checked.) **Conditional, not counted**: under not-LOW, $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\hat\zeta_H)+1})`$.

- **Not proved** (open; the exact long reaches for $`D \lt G(\hat\zeta_3)`$ with PSI-θ at $`\theta_2+1`$, [SHIFT6.md](SHIFT6.md) §1.1, have a blocking point at some codes, §2.1 there): exact long reaches for $`D \gt \hat G`$ (outline below $`\Phi^{\hat G}`$, the analogue of $`\Phi'`$ over $`\hat G`$, read at the base $`F_\lambda`$; from $`\Phi^{\hat G}`$ on they need PSI-θ at the
  index $`\theta_2 + 1`$, which is not proved; this is where the realizer reading and the cap reading still differ); READ$`^\sharp`$ past $`\hat\zeta_H`$ (conjecture; the first overshoot by a
  restart's own prefix is at $`\hat\zeta_f`$; at $`\Omega_k`$, $`k \ge 4`$, and at $`\Omega_\omega`$ the hulls nest); READ$`^\sharp`$ at every normal multiplier would give CAP-0 below $`P'`$, hence not-LOW; LOW; (P); (Q′).
- The referee's other minor points: NO-READL depends on the new EXACT-LONG$`^G`$ and EXACT-F (NO-LIT did not); one line on the caps of long intermediate restarts (they lie in the
  domain of the transport); one missing line on the domain of the realizer map; a remark on offsets above the bound of the transport lemma, which earlier referees accepted. (All applied in the twenty-seventh round, [SHIFT6.md](SHIFT6.md) §1.1.)

### 2.2 $`\nu_C = \nu_S`$: the tools at every level, and TC⁺ at every level

Notation of §1.2; $`m^*_\xi = \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$ (the start of level $`1+\xi`$), and LOW$`^\infty`$: $`\nu_C \lt \upsilon^\infty`$ (§1.3), which follows from LOW$`^\omega`$.

- **The minor points of the review of §1.2 are applied** (proved, **2 reviews**): both halves of TC⁺ need FRAG; D-UNC$`^Z`$ is not a case of D-UNC$`^\pi`$ at level 1 (it is at higher
  levels); which part of the dictionary is used. **Not proved**: the rewritten pin of long prefixes (the citation of the region transport, and two cases for the image), in the case
  where the atoms of the code lie in regions that are moved (blocking point, below).
- **TAIL-LEVEL, OFF-INF$`^{\mathrm{lev}}`$, REAL$`^{\mathrm{lev}}`$, CEIL$`^{\mathrm{lev}}`$** (proved). The induction on final segments never leaves the level of the restart; the offset lemma, the realizers of every
  code below $`\pi_\eta`$, and the ceilings hold at every level. In the earlier proofs every bound "below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$" is used only to put $`\eta`$ in $`D`$, and the paper lists each
  place with its replacement. (A side correction: the rule of [SHIFT4.md](SHIFT4.md) §2.1 that a tail of EXACT-CL\* stays in its segment needs the start of the tail above $`H(z_0)`$, as
  the proof chooses; with the wording as it is, $`\nu = H(\omega^\omega + \omega^2)`$ is a counterexample.)
- **The tools at every level** (proved by transfer; given FRAG where the source uses it). EXACT-C, EXACT-CL\*, GAP$`_j`$, the cap R-CAP\*, LONG-CLASS, the pins (FAR-PIN, MULTI-RC\*, PIN-IDX,
  PIN-ALL, TOP-REG-FAR), EXACT-LONG and CROSS-O for $`D \lt G_2`$, EXACT-LONG-CL\*, EXACT-G($`\Omega_3`$), the θ and θ⁺ tiers, READ below $`\hat\zeta_2`$ and below $`\hat\zeta_3`$, SEP$`^{G_2}`$, CAP-0 below $`G(\hat\zeta_3)`$,
  BC$`^\pi`$ (also between restarts at different levels) and READ-EQ hold at every level $`\ge 1`$, for restarts below $`\min(\nu_S, \upsilon^\infty)`$. (The referee: the cap of the θ tier is proved only at
  the level of the dictionary and the refereed inventory; the audit table should get rows for it.)
- **TC⁺ at every level, MONO-F** (proved, given FRAG). For every base change $`B`$ of BC$`^\pi`$ between restarts at any levels (absorption allowed): $`r(BR) = B(r(R))`$ for every short
  restart with $`\tau \lt G_2`$, every long restart with code $`G_2\cdot D + m_0`$, $`D, m_0 \lt G_2`$, and at the code $`G(\Omega_3)`$. At level 1 this is TC⁺ of §1.2, now with **2 reviews**; at level 2 it
  is new.
- **Theorem X$`^{(1+\xi)}`$ improved** (proved, given FRAG; every $`\xi \ge 1`$): $`\nu_C`$ is not in $`(m^*_\xi, Y'_\xi)`$, with $`Y'_\xi = \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi) + \omega^{G(\hat\zeta_3)+1}) \gt Y_\xi`$ (§1.3).
  **Conditional, not counted**: if $`\nu_C \gt m^*_\xi`$ and $`\xi \lt I_\omega`$, the claim holds in $`R_2^C`$ on $`[0, Y'_\xi]`$; under not-LOW, $`\nu_C \ge Y'_1`$.
- **Conditional, not counted** (correct under LOW$`^\infty`$, given FRAG): the bookkeeping, the room and the zone system of §1.2 for the (D1b) spans whose η-offset is below $`\omega^{G_2^2}`$.
  **Blocking point**: the pin of a long prefix whose code has atoms in moved regions needs a form of PIN-ALL for moved lower atoms, which is not written (the referee thinks it can be
  repaired; it is repaired in the twenty-seventh round, [SHIFT6.md](SHIFT6.md) §1.2). Until then the pins, the far TOP-REG, the placement PLACE$`^{T2}`$, RES-ALL$`^{T2}`$ and the residue below hold only for spans whose long prefix codes have no such atoms.
  So the blocking point of §1.2 moves: the level-2 tools are now proved, and what is missing is this pin and LOW$`^\infty`$.
- **The residue** (the paper's assembly, after the blocking point is repaired). $`\nu_C = \nu_S`$ would follow from: exact reaches that commute with base change for codes in
  $`[G_2^2, \Omega_2)`$; caps for codes $`\ge G(\hat\zeta_3)`$ (room); the inspection after TWIST (outline); and LOW$`^\infty`$ (open). $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$ are both **open**.
- The referee's other minor points: the paper says that an earlier blocking point on TC⁺ is lifted, which overclaims, since the route now rests on LOW$`^\infty`$; one case of the cross-level base change
  ($`a' = m^*_\xi`$) is missing but holds; code 0 gives no restart. (Applied in the twenty-seventh round, [SHIFT6.md](SHIFT6.md) §1.2.)

### 2.3 Native codes: decorations as stage regions, and $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$

Words of [SHIFT3.md](SHIFT3.md) §1.2 and §1.3: stages, pair blocks, chain number. A **decoration** is an element $`e`$ with $`e \le_1 v`$ for some $`v \gt e`$ that is not in a pair.

- **SUPPLY-0** (proved). If $`e \le_1 v`$ with $`v \gt e`$, then for every $`\xi \lt e`$ an additive principal copy of $`e`$ lies in $`(\xi, e)`$ (Carlson's rule R1 at $`e`$ with the set $`\{e\}`$).
  So a decoration supplies free levels, as the roots of a pair do, but it is not a pair and adds no link to a chain. The second pair that §1.3 said the stages from
  $`\omega^\omega`$ on need (chain number 4) is not needed.
- **Regions** (proved: WT, DEC-SUP, DEC-REGION). For every stage $`1 \le T \lt \varepsilon_0`$ a pair-free region code built from nested decorations, each followed by a free carrier; a decoration
  supplies units of every lower kind below itself (DEC-SUP), and for $`T' \lt T`$ the region of $`T'`$ is realized inside that of $`T`$ (DEC-REGION). Below $`\omega^\omega`$ these are the free levels of the
  pair blocks. (The referee re-ran the construction on 42,901 pairs $`T' \lt T`$ with own code, 0 errors; two broken versions are caught.)
- **The native side with regions** (proved). The shape, top and row lemmas and the hosting lemma of the pair blocks hold with the regions in place of the free levels; the patterns are
  fan-free and have chain number at most 2.
- **The ordinal side for $`T \lt \varepsilon_0`$** (proved by transfer). The counting rule for $`\psi`$ over the base $`\Omega_\omega`$ and the lemmas on the parameters of §1.3 hold for every stage
  below $`\varepsilon_0`$; only two inputs depend on $`T`$, and both hold below $`\varepsilon_0`$. (The referee: the list of inputs that depend on $`T`$ is incomplete, but every omitted one holds for any $`T`$.)
- **PUSH$`^{\varepsilon_0}`$** (proved; chain length 3). Natively, for every $`1 \le S \lt \varepsilon_0`$, $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot(1+S))`$, hence

```math
\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0),
```

and $`\iota(\mathrm{CH}_4) \gt \psi_{\Omega_1}(\Omega_\omega\cdot T)`$ for every $`T \lt \varepsilon_0`$. Before, $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$. So RED-TOWER covers every $`t \lt \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$ natively.
- **Conditional, not counted** (now proved, [SHIFT6.md](SHIFT6.md) §1.3): $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ is the least fixed point of $`T \mapsto \psi_{\Omega_1}(\Omega_\omega\cdot T)`$ (checked; the proof is an outline). STAGE-TOWER (outline): a whole
  lower system of codes as the code of a stage label; with the ordinal side for countable labels $`\ge \varepsilon_0`$ (outline) it would give $`\sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$.
  (The referee: two gaps sit inside the outline: there is no single system below $`Z_\omega`$, so the systems below each $`Z_n`$ must be used one by one; and the copied label needs a carrier
  and must be shown to lie above the base. Both are done in the twenty-seventh round, [SHIFT6.md](SHIFT6.md) §1.3.)
- **Open**: a pair-free region code past $`\varepsilon_0`$ with chain number 2; labels of the form $`\Omega_\omega\cdot\xi`$ with $`\xi \ge \Omega_1`$ (their codes carry parameters, which the stage systems
  exclude); labels $`\ge \Omega_\omega`$. $`\theta_0`$ lies far above: $`\psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0) \lt \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1) \lt \psi_{\Omega_1}(\Omega_{\omega+1}) \lt \psi_{\Omega_1}(\Omega_{\Omega_\omega}) \lt \theta_0`$ (checked, Python and Lean).
- The referee's other minor points: one lemma part is never needed; the closure of the old and new elements should be stated; the second pair is "not needed" rather than "false";
  one comparison should cite HOST$`_4`$; one sample has no certificate (checked by hand; nothing proved rests on it); Carlson 2001 (pp. 19–20) only announces the identification that the
  paper quotes. (Applied in the twenty-seventh round, [SHIFT6.md](SHIFT6.md) §1.3.)

### 2.4 Status after the twenty-sixth round

The twenty-seventh round changed this status; see [SHIFT6.md](SHIFT6.md) §1.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{21}]`$ given FRAG ($`[0, X_{18}]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$. No InaccPsi upper
  bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches: exact (given FRAG) for every short restart with $`\tau \lt G_2`$ and every long restart with $`D \le \hat G`$; caps for every code below $`G(\hat\zeta_H)`$, in the hull form; the landing cap
  READ$`^L`$ is false.
- Names: no change (every $`\upsilon`$-point below $`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ has the name $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$).
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on all 3,166 sample matrices (no change); natively $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$ and
  $`\iota(\mathrm{CH}_2) \ge \Theta_1`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: LOW is not decided; CAP-0 holds for every code below $`G(\hat\zeta_H)`$ (given FRAG); the tools and TC⁺ below $`G_2^2`$ hold at every level. Left: the pin with moved atoms,
  LOW$`^\infty`$, (D1b), (E4).

### 2.5 Checks of the twenty-sixth round

Each run was under 60 seconds; none is a proof.

- §2.1. Names, normal forms, readings and the order chain $`X_{19} \lt X_{20} \lt X_{21} \lt H(\Omega_4)`$ in Python and Lean (green, identical); the exponents of 899 normal multipliers in $`[\hat\zeta_3, \Omega_4)`$, the
  margins, D-UNC on 1,800 offsets, the ceilings at three multipliers: 0 failures. The referee: the ceiling at $`\hat\zeta_A`$ by proof; the witness lies in $`D`$ and below $`X_{20}`$; 743 normal
  multipliers (none below $`\hat\zeta_H`$ with an exponent $`\ge \hat G + G_2`$), monotonicity on 23,801 pairs: 0 failures; the Lean rerun is identical.
- §2.2. Frontier chains and normal forms at 10 levels (from 1 to $`I_0`$); the realizer form of D-UNC$`^\pi`$ on 4,768 tests; offsets on 330 tests; TAIL-LEVEL on 193 samples: 0 failures; Lean green.
  The referee: hull membership on 4,432 tests, realizers for 483 of 483 codes, ceilings and monotonicity on 131 tests and 13,366 pairs, 1,110 memberships in $`D_\infty`$: 0 failures; the author's
  tests re-run with the same results; Lean green, identical.
- §2.3. 17 new code and top patterns: patterns, closed, fan-free, chain number 2. Certificates (replayed): forward 12 of 13, tops below $`\mathrm{CH}_3`$ 3 of 4, extra 4 of 5, reverse 0 of 6.
  62 name checks: 0 failures; Lean green. The referee: own re-implementation of the regions (above), the author's runs byte-identical, 2 certificates reproduced; the Lean rerun is identical.

### 2.6 Open

The twenty-seventh round changed this list; the current list is [SHIFT6.md](SHIFT6.md) §1.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past $`G(\hat\zeta_H)`$ and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{21}`$ given FRAG: exact long reaches for $`D \gt \hat G`$ (outline below $`\Phi^{\hat G}`$; past it, PSI-θ at the index $`\theta_2 + 1`$); READ$`^\sharp`$ past $`\hat\zeta_H`$ and at every $`\Omega_k`$;
  the exact reach at the code $`G(\hat\zeta_A)`$; the lower-bound side of the tiers above $`\Omega_3`$.
- The first inaccessible: native region codes past $`\varepsilon_0`$, uncountable stage labels, labels $`\ge \Omega_\omega`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\hat\zeta_H), P')`$); LOW$`^\infty`$; the pin of long prefixes with moved atoms; TC⁺ for codes $`\ge G_2^2`$; caps for codes $`\ge G(\hat\zeta_3)`$ in the
  placement; (D1b), (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{21}`$; the rest of
  [COVER.md](COVER.md) §9.
