[← Back](README.md) | [English](SHIFT5.md) | [Japanese](SHIFT5-ja.md)

# $`R_2^+`$, the twenty-fifth round: $`\nu_C \ge X_{19}`$ given FRAG, the landing cap, TC⁺ below $`G_2^2`$, and GEN for every η

This page continues [SHIFT4.md](SHIFT4.md) (§2 there is the twenty-fourth round). The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

Three papers (2026-10), each refereed once, so a result on this page has 1 review unless a count is given. **2 reviews** means that a referee of the
twenty-fourth round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. Papers cited here: [W07a]
(L.3.30, L.4.7) and [W07b] (L.2.1, Thm 2.2, Def 4.1, the proof of Thm 5.3), as in [SHIFT4.md](SHIFT4.md) §1. No Lean file was added: two papers (§1, §3) checked a Lean file
that only compares terms (`#eval`, no theorem; green, and green in the referees' reruns), and the referee of §2 wrote one of the same kind (green), so these count as checks.
The minor points of the twenty-fourth-round reviews are applied: those of [SHIFT4.md](SHIFT4.md) §2.1 and §2.2 by the paper of §1 (checked again by its referee, **2 reviews**),
the label point of §2.4 there by §3, and the rest in [SHIFT4.md](SHIFT4.md) §2. Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher than in the papers):
level 1 is below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$.

Notation of [SHIFT4.md](SHIFT4.md): $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$, $`G_2 = G(\omega^2)`$, $`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$,
$`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$, the reading $`R`$ of §2.2 there, and $`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$. New names of this round (with $`\hat\zeta_2`$ of [SHIFT4.md](SHIFT4.md) §2.2):

```math
\hat\zeta_3 = \theta_3\cdot\omega^2,\quad g_3 = \psi_{\Omega_3}(\Omega_\omega + \hat\zeta_3),\quad \varepsilon_+ = \varepsilon_{G_2+1},\quad \hat\zeta_4 = \hat\zeta_3 + \omega^{\omega^{g_3\cdot 2}},\quad \hat\zeta_\varepsilon = \hat\zeta_3 + \varepsilon_{g_3+1},
```

with $`R(\hat\zeta_3) = G_2`$, $`R(\hat\zeta_4) = \omega^{G_2^2}`$, $`R(\hat\zeta_\varepsilon) = \varepsilon_+`$, and $`\hat\zeta_2 \lt \hat\zeta_3 \lt \hat\zeta_4 \lt \hat\zeta_\varepsilon \lt \Omega_4`$ (checked).

## 1. The landing cap: $`\nu_C \ge X_{19}`$ given FRAG

- **The minor points of the twenty-fourth-round reviews of [SHIFT4.md](SHIFT4.md) §2.1 and §2.2 are applied** (proved, **2 reviews**). Among them: the false step of the proof of $`X_{18}`$
  is replaced by a lemma on least multiples (the least multiple of $`\omega^e`$ above $`\gamma`$ is $`\ge \gamma + \omega^{e'}`$ for $`e' \le e`$); D-UNC$`^{\mathrm{SEG}}`$ for bases $`\eta \ge \Omega_2\cdot a`$ (the case that was used and not stated);
  the successor step of the reading derived from the counting rule PSI-n; the tail bases above $`H(\Omega_3)`$; the non-separation at $`\tau_{\mathrm{LH}}`$ is only a remark (below). So the proofs of
  $`X_{17}`$ and $`X_{18}`$, with these repairs, have **2 reviews** (the referee of §2 also redid the last step of the proof of $`X_{18}`$).
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

- **Not proved** (open): the landing cap at every normal multiplier below $`\Omega_\omega`$ (conjecture READ$`^L`$; it would give CAP-0 for every code below $`P'`$, hence not-LOW); exact long reaches for
  $`D \ge \varepsilon_+`$ (outline: the same proof through the base changes of [SHIFT2.md](SHIFT2.md) §1.1, up to codes $`G(\Omega_1)`$); past $`G(\Omega_1)`$ the realizer reading and the cap reading differ, and no
  general separation is known; LOW; (P); (Q′).
- The referee's other minor points: the fallback cites the wrong check (it needs that every exponent on $`[\hat\zeta_3, \hat\zeta_4)`$ is below $`G_2^2`$; the referee's test shows it); one output labels
  a point "X19" that is not $`X_{19}`$; the ceiling at $`\hat\zeta_\varepsilon`$ should cite the referee's test; one case ($`D = 0`$) of the crossing lemma of EXACT-LONG⁺ must be defined on its own.

## 2. $`\nu_C = \nu_S`$: TC⁺ below $`G_2^2`$ and the spans below $`\omega^{G_2^2}`$

Notation of [SHIFT3.md](SHIFT3.md) §1.4 and §2.4 (TC⁺, LOW, LOW$`^\omega`$, (D1b), (E4)); $`\pi_\eta = \psi_{\Omega_2}(\Omega_\omega + \theta\cdot\eta)`$. Every proved result of this section is at level 1.

- **D-UNC$`^\pi`$** (proved, no FRAG). For $`\eta \in D`$ and a normal form $`\xi \lt \pi_\eta`$: $`\eta + \xi \in D`$ iff the constants of $`\xi`$ are below $`H(\eta + \xi)`$; summands of $`\eta`$ may be absorbed.
  (The referee: D-UNC$`^Z`$ of [SHIFT4.md](SHIFT4.md) §1.4 is not a case of it, contrary to the paper; at $`\eta = 1, 2, \omega^2`$ the offset $`\xi = \pi_\eta \lt Z`$ gives $`\eta + \xi \in D`$, which D-UNC$`^\pi`$ does not cover.)
- **BC$`^\pi`$** (proved at level 1, no FRAG). The η-base changes are defined on all offsets below a constant-free bound $`\Gamma \le \pi_\beta`$, with absorption at the target allowed; in the setting of
  $`\nu_C = \nu_S`$ every base is above $`H(\hat\zeta_2)`$, so $`\Gamma = G(\hat\zeta_2)`$ works.
- **READ-EQ** (proved). A base change commutes with the reading $`\Theta`$ on codes below $`G_2`$. This settles a minor point of the review of [SHIFT3.md](SHIFT3.md) §1.4.
- **TC⁺ below $`G_2^2`$, MONO-F** (proved, given FRAG, at level 1). A base change $`B`$ keeps reaches, $`r(BR) = B(r(R))`$, for every short restart with $`\tau \lt G_2`$, every long restart with code
  $`G_2\cdot D + m_0`$, $`D, m_0 \lt G_2`$, and at the code $`G(\Omega_3)`$; so the code transport holds for every such base change. The exact reach is strictly increasing in the code below $`G_2^2`$. (The referee:
  both halves need FRAG; the paper's "the half ≤ needs no FRAG" is wrong.) Past $`G_2^2`$ only brackets are known.
- **The cap below $`G(\hat\zeta_3)`$ again** (proved by transfer, given FRAG): the same route as §1 gives CAP-0 below $`G(\hat\zeta_3)`$ and $`\nu_C \ge X_{\hat\zeta_3} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_3 + \omega^{G(\hat\zeta_3)+1}\cdot 2)`$, a point below $`X_{19}`$.
  **Not proved**: the matching bound under not-LOW (it needs these caps at level 2). (The referee: normality of the multiplier is essential; a non-normal $`\zeta \lt \hat\zeta_3`$ can have $`R(\zeta) \ge G_2`$.)
- **Conditional, not counted** (correct under LOW, given FRAG; the paper claims them under LOW$`^\omega`$). For every (D1b) span whose η-offset is below $`\omega^{G_2^2}`$: the bookkeeping past every index fixed point,
  room below $`G(\hat\zeta_3)`$, pins at exponents below $`G_2^2`$ with a far TOP-REG, and TC⁺ at every recorded restart (U0–U3); so these spans are placed (PLACE$`^{T2}`$, RES-ALL$`^{T2}`$), and
  $`c_u = H(\eta_u + \omega^{G_2^2})`$ is a zone system (ZONE$`^{(2)}`$). **Blocking point**: LOW$`^\omega`$ adds only the case $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, which the conjectured names predict, and there these
  steps need the level-2 forms of the exact long reaches, of CROSS-O and the pins, of the cap below $`G(\hat\zeta_3)`$, of LONG-CLASS and of BC$`^\pi`$, none of which is proved. So the blocking point of the
  review of [SHIFT3.md](SHIFT3.md) §1.4 (everything there under LOW) still stands.
- **The residue** (the paper's assembly, with LOW for LOW$`^\omega`$ and one outline step). $`\nu_C = \nu_S`$ would follow from: exact reaches that commute with base change for long codes $`\ge G_2^2`$;
  caps for codes $`\ge G(\hat\zeta_3)`$ (room); the inspection after TWIST (outline); and LOW. §1 gives exact long reaches for $`D \lt \varepsilon_+`$ and caps below $`G(\hat\zeta_\varepsilon)`$, but no paper shows that they
  commute with base change. $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$ are both **open**.
- The referee's other minor points: one citation in the pins (the region transport, not READ-EQ); one place uses the dictionary that the paper says it does not use; the first open case has
  code $`G_2^2 + 1`$, not $`G_2^2`$.

## 3. GEN for every η, and native codes up to $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$

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

## 4. Status after the twenty-fifth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{19}]`$ given FRAG ($`[0, X_{18}]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$. No InaccPsi upper
  bound for $`\nu_C`$: (P) at a named pair stays open.
- Reaches: exact (given FRAG) for every short restart with $`\tau \lt G_2`$ and every long restart with $`D \lt \varepsilon_+`$; caps for every code below $`G(\hat\zeta_\varepsilon)`$.
- Names: every $`\upsilon`$-point below $`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ has the name $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on all 3,166 sample matrices (no change); natively $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$ and
  $`\iota(\mathrm{CH}_2) \ge \Theta_1`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: LOW is not decided; CAP-0 holds for every code below $`G(\hat\zeta_\varepsilon)`$ (given FRAG); TC⁺ holds below $`G_2^2`$ at level 1. Left: (P1), (D1b), (E4).

## 5. Checks of the twenty-fifth round

Each run was under 60 seconds; none is a proof.

- §1. Names, normal forms, readings and the order chain $`X_{17} \lt X_{18} \lt \dots \lt X_{19}^- \lt X_{19} \lt H(\Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ in Python and Lean (green); the exponents of 3,000 normal multipliers,
  the margin, the order on 861,202 pairs, D-UNC on 2,400 landing offsets, the ceiling and the least-multiple lemma: 0 failures. The referee: the witness against the fine cap; the ceiling at
  $`\hat\zeta_\varepsilon`$ on 611 samples; the exponents near $`\hat\zeta_4`$ and $`\hat\zeta_\varepsilon`$ (30,338 pairs); D-UNC on 1,572 offsets; the margin on 198,787 pairs: 0 failures; the Lean rerun and an own Lean file are green.
- §2. The tier bounds, $`R(\hat\zeta_3) = G_2`$, 1,039 multipliers, D-UNC$`^\pi`$ on 4,423 offsets (1,532 with absorption), the atom substitution on 388 codes: 0 failures (Python only). The referee: 238 normal
  multipliers, D-UNC$`^\pi`$ on 1,219 offsets at bases of level 3: 0 failures; a Lean file of the order chains, green.
- §3. The maps $`B`$ of STEP and $`E`$ of LOW-STEP with 15 arguments $`A`$ from $`\Omega_\omega\cdot\omega`$ up to $`I_\omega + \theta`$ (about 6 million pairs), the normal-form test on 1,620 values at 9 levels, D-UNC on 2,016 tests,
  the codes on 429 samples: 0 failures; three broken variants of $`E`$ fail. Lean green. The referee: extraction on other hulls (8,012 tests), strict increase of $`H`$ and $`\pi`$ (25,440 pairs), D-UNC with
  offsets in $`[P_\xi, \pi_\eta)`$ (792 tests), $`B`$ and $`E`$ with countable atoms in $`A`$ (about 600,000 pairs): 0 failures; the Lean rerun is identical.

## 6. Open

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps past $`G(\hat\zeta_\varepsilon)`$ and a lower bound at code $`P'`$; (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{19}`$ given FRAG: exact long reaches for $`D \ge \varepsilon_+`$ (outline up to $`G(\Omega_1)`$); a separation past $`G(\Omega_1)`$; the landing cap at every $`\Omega_k`$ (READ$`^L`$);
  the lower-bound side of the tiers above $`\Omega_3`$.
- The first inaccessible: native stages $`\ge \omega^\omega`$, uncountable stage indices, $`\Omega_{\omega+1}`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[G(\hat\zeta_\varepsilon), P')`$), LOW$`^\omega`$ (now: the level-2 forms of the tools of §2), TC⁺ for long codes $`\ge G_2^2`$, caps for codes $`\ge G(\hat\zeta_3)`$ in the
  placement, (D1b), (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names beyond $`X_{19}`$; the rest of
  [COVER.md](COVER.md) §9.
