[← Back](README.md) | [English](SHIFT3.md) | [Japanese](SHIFT3-ja.md)

# $`R_2^+`$, the twenty-first round: $`\nu_C \ge X_{13}`$ given FRAG, the hierarchies $`\vartheta_D`$ on both sides, pair blocks, BIN-SHAPE for every $`n`$, and TC⁺ under LOW

This page continues [SHIFT2.md](SHIFT2.md) (§3 there is the twentieth round); §1 is the twenty-first round. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

## 1. The twenty-first round

Four papers (2026-10), each refereed once, so a result in this section has 1 review unless a count is given. **2 reviews** means that the referee of
the twentieth round proposed the repair (or checked the result) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. Papers cited here: Wilken,
"Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) (below [W07a]); Carlson–Wilken, "Tracking chains of Σ₂-elementarity", APAL 163 (2012)
([link](https://www.sciencedirect.com/science/article/pii/S0168007211001199)). No Lean file was added: one paper (§1.1) checked a Lean test file of named points with leanman, and one
referee (§1.4) wrote a Lean file that compares the bounds of a check (both green; they only compare terms, `#eval`, no theorem), so they count as checks. The minor
points of the twentieth-round reviews are applied, in [SHIFT2.md](SHIFT2.md) §3 and below. Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher than in the papers).

### 1.1 The hierarchies $`\vartheta_D`$ on both sides: $`\nu_C \ge X_{13}`$ given FRAG; (P) still open

Notation of [SHIFT2.md](SHIFT2.md) §3.1. Let $`U`$ be $`\Omega_1`$, $`\Omega_2`$ or $`\Omega_3`$. An index $`D \le \varepsilon_{U+1}`$ is written in base-$`U`$ Cantor normal form, and $`K_U(D)`$ is the set of its
coefficients at all depths. $`C^U_0`$ is the set of $`\varepsilon`$-numbers below $`U`$, and for $`D \ge 1`$, $`C^U_D`$ is the set of $`b \in C^U_0`$ that are fixed points of the enumeration of every
$`C^U_{D'}`$ with $`D' \lt D`$ and $`K_U(D') \subset b`$. This is the absolute form of the hierarchy $`\vartheta_D`$ of [SHIFT.md](SHIFT.md) §9.2. $`\mathrm{ex}^X_D(\eta)`$ is the $`\eta`$-th element of
$`(C^U_D \setminus C^U_{D+1}) \cap (X, U)`$ (the exact-level enumeration). New names:

```math
\Phi^\vartheta_\Omega = \psi_{\Omega_2}(\varepsilon_{\Omega_2+1}),\qquad \Phi^\vartheta_2 = \psi_{\Omega_3}(\varepsilon_{\Omega_3+1}),\qquad \mathbb{G}^\vartheta = G(\Phi^\vartheta_2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Phi^\vartheta_2}).
```

- **The minor points of the twentieth-round review are applied** (proved, **2 reviews** for the repaired statements). **TOP-REG-FAR′**: the far upper-bound rule also holds at the first
  block when the candidate is at least the reach of the restart at the target; it is now a lemma of its own (the only steps that depend on the block are this bound and one index
  inequality), and EXACT-LONG uses it. The missing line of LB is added. Correct example restarts for NO-PHI are given (the refutation is unchanged). The hull lemma one level up
  (HULL-Ψ3) is stated and proved; HULL-θ3 below replaces it. Three wording points.
- **The hierarchies for every $`U`$** (proved). CLUB, normal forms and the comparison rule hold for every $`C^U_D`$. **AGREE**: the $`\vartheta_D`$ of [SHIFT.md](SHIFT.md) §9.2 enumerates
  $`C^{\Omega_2}_D \cap (\Omega_1, \Omega_2)`$. **VEB-Ψ**: the hierarchy of [SHIFT2.md](SHIFT2.md) §2.1 is the part $`C^U_{U+v}`$ of this one. **LEVEL** and the order rule **T1~**: with $`k = \max(K_U(D) \cup \{\eta\})`$
  and $`k'`$ likewise, $`\mathrm{ex}_D(\eta) \lt \mathrm{ex}_{D'}(\eta')`$ iff $`D \lt D'`$ and $`k \lt \mathrm{ex}_{D'}(\eta')`$, or $`D = D'`$ and $`\eta \lt \eta'`$, or $`D' \lt D`$ and $`\mathrm{ex}_D(\eta) \le k'`$. The forms
  TmTh (constants, the base, sums, Veblen $`\varphi`$ for values that are not strongly critical, and $`\mathrm{ex}_D(\eta)`$ with $`D \ge U`$ for strongly critical values) are unique, cover
  an initial segment of $`(X, U)`$, and are decided alike at every base (**UNIF-θ**). (The referee: two side conditions are not proved but follow from the same proofs; additivity in
  UNIF-θ needs an additive map.)
- **Wilken's side** (proved; it uses only [W07a] L.3.30, L.4.2–4.4 and Thm 3.23). Let $`\tau`$ be $`1`$ or a $`\upsilon`$-point. Every $`\varepsilon`$-number $`\alpha \in (\tau, \tau^\infty)`$ is
  $`\theta^\tau(\Omega_1\cdot(1+E_\alpha) + \eta)`$, and for every index $`E \le \varepsilon_{\Omega_1+1}`$ with $`K(E) \subset \alpha`$: $`\alpha \in C^{\Omega_1}_E`$ iff $`E_\alpha \ge E`$ (**VEB-THETA$`^\vartheta`$**), and
  $`\theta^\tau(\Omega_1\cdot(1+E) + \eta) = \mathrm{ex}^\tau_E(\eta)`$ (**EXACT-LEVEL$`^\vartheta`$**). So Wilken's terms and the forms are the same terms. Wilken's relativized Bachmann–Howard point
  $`\theta^\tau(\varepsilon_{\Omega_1+1})`$ is the least element of $`C^{\Omega_1}_{\varepsilon_{\Omega_1+1}}`$ above $`\tau`$, and every $`\upsilon`$-point lies in $`C^{\Omega_1}_{\varepsilon_{\Omega_1+1}}`$. (The referee: one citation of
  [W07a] L.4.3 for $`\theta_1`$, where the paper states it only for $`\theta^\tau`$, needs a one-line repair from L.4.2 and L.3.30.)
- **Base change** (EXACT-θ, proved). Wilken's base change from one $`\upsilon`$-point to a smaller one sends the value of every form at the first point to its value at the second, also with a
  parameter map. No fixed-point lemma is needed.
- **The InaccPsi side** (PSI2-θ, proved; the referee re-derived the main steps). $`\psi_{\Omega_2}(\beta)`$ for every $`\beta \lt \varepsilon_{\Omega_2+1}`$ is given by a counting rule with stops. Write
  $`\beta = \Omega_2^{E_1}\cdot c_1 + \dots + \Omega_2^{E_k}\cdot c_k`$ and $`R_E = C^{\Omega_2}_{\Omega_2+E}`$. Start at $`A_0 = \Omega_1`$. Step $`i`$ takes the $`c_i`$-th element of $`R_{E_i}`$ above $`A_{i-1}`$ if it lies
  below $`A^+_i`$, the next element of $`R_{E_i+1}`$ above $`A_{i-1}`$; otherwise the rule stops with the value $`A^+_i`$. The arguments with no stop are exactly the arguments of normal forms,
  and an exponent may be larger than the value before it (the "parameter lag"). So $`\psi_{\Omega_2}(\varepsilon_{\Omega_2+1}) = \Phi^\vartheta_\Omega`$, and **the conjecture of [SHIFT.md](SHIFT.md) §9.2 holds**:
  $`\Xi_2 = \psi_{\Omega_2}(\varepsilon_{\Omega_2+1})`$, the Bachmann–Howard ordinal relativized to $`\Omega_1`$. CONV (the dictionary between the two term languages), SUBT, CNST and the hull lemma
  HULL-SEG give (R4): a code $`\tau \lt \Phi^\vartheta_\Omega`$ is in the hull exactly when its constants are. One level up: $`\Phi^\vartheta_2 = \psi_{\Omega_3}(\varepsilon_{\Omega_3+1})`$ (PSI3-θ), and HULL-θ3.
- **Theorem EXACT-O$`^\vartheta`$** (proved; "$`\le`$" without FRAG, "$`\ge`$" given FRAG). Every restart $`\nu`$ with $`\rho_{\nu+\omega^2} \le \nu_S`$ and $`\tau_\nu \le \Phi^\vartheta_\Omega + 1`$ has
  $`r(\nu) = \delta_\nu + o_\nu(\tau_\nu)`$; at $`\tau_\nu = \Phi^\vartheta_\Omega`$ this is $`\delta_\nu + \theta^{\rho_\nu}(\varepsilon_{\Omega_1+1})`$. EXACT-O of [SHIFT2.md](SHIFT2.md) §3.1 is the part $`\tau_\nu \le \Phi^\chi_\Omega + 1`$.
- **Long restarts** (proved, given FRAG). R-CAP$`^O`$, LB, **EXACT-LONG** $`r(\lambda) = r(\nu) + o_\nu(m_0)`$ and **CROSS-O** hold for $`m_\lambda = G_2\cdot D + m_0`$ with $`D, m_0 \lt \Phi^\vartheta_\Omega`$, so crossing is
  sharp at every index distance $`\omega^2\cdot x`$ with $`x \le \Phi^\vartheta_{\rho_\lambda}`$.
- **The θ-tier of η-offsets and multipliers** (proved, given FRAG, as a list of substitutions into [SHIFT2.md](SHIFT2.md) §3.1; the referee checked that every input special to the old
  language has a replacement): η-offsets below $`\Phi^\vartheta_\Omega`$ (uncountable ones included), multipliers below $`\Phi^\vartheta_2`$, **R-CAP$`^\vartheta`$** for every code $`G_2 \le m \lt \mathbb{G}^\vartheta`$ (so the
  interval $`[\mathbb{G}^\chi, \mathbb{G}^\vartheta)`$, which had no upper bound, now has one), **CEIL$`^\vartheta`$** (no FRAG), **CROSS-SHARP$`^\vartheta`$**. (The referee: one example of the level reading, written
  as a substitution, is false as written; it must be the full shift $`\Omega_k \mapsto \Omega_{k-1}`$; it is not used elsewhere.)
- **Theorem X13** (proved, given FRAG). As X12, with R-CAP$`^\vartheta`$ and CEIL$`^\vartheta`$:

```math
\nu_C \ge X_{13} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Phi^\vartheta_2} + \omega^{\mathbb{G}^\vartheta+1} + \omega^{G_2+1}),\qquad \Phi^\vartheta_2 = \psi_{\Omega_3}(\varepsilon_{\Omega_3+1}).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{13}]`$, both halves, given FRAG**, and $`X_{12} \lt X_{13} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. Without FRAG the range stays $`[0, X_4]`$. Also
(P-LOW$`^\vartheta`$) every restart $`a`$ with (P) has $`e_a \ge \mathbb{G}^\vartheta + 1`$.

- **Not proved** (open, as the paper says): (P) and (Q′) at $`(L(\omega), L(\omega+1))`$ or at any named pair, and so an InaccPsi upper bound for $`\nu_C`$. Missing: exact caps for short restarts
  with $`\tau \in (\Phi^\vartheta_\Omega + 1, G_2)`$, and for long restarts with $`D \ge \Phi^\vartheta_\Omega`$ or $`m_0 \ge \Phi^\vartheta_\Omega`$ (for codes $`\ge \mathbb{G}^\vartheta`$, where the predecessors in (P) now are, there is
  no upper bound at all); η-offsets at or above $`\Phi^\vartheta_\Omega`$, multipliers at or above $`\Phi^\vartheta_2`$. Each tier moves the predecessors in (P) just above its own cap region.
- **Next.** The tier of $`n`$-ary hierarchies up to $`\theta`$: Wilken's side and base change go level by level (outline); the InaccPsi side, **PSI-n**, is open. In Buchholz's hull
  $`\psi_{\Omega_3}(\zeta)`$ is generated only for $`\zeta \lt \beta`$, so the index of $`\psi_{\Omega_2}(\beta)`$ is a collapse of $`\beta`$ itself; what is missing is a counting rule over two levels.
  Codes in $`[\theta, G_2)`$: open (they need (R4) above $`\pi_g`$ and the upper-bound rule past $`\delta\cdot\omega`$). Conjecture EXACT-O$`^n`$: the same up to $`\theta`$, which would give the range
  $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2\cdot 2} + \omega^{G(\theta_2)+1} + \omega^{G_2+1})`$.
- Remark: EXACT-O$`^\vartheta`$ and EXACT-LONG have the shape of Carlson–Wilken 2012, Cor 7.13 (a reach is the value of a later chain point plus a degree read there); there the description
  is exact because the coding is onto, here because TmTh is onto below $`\Phi^\vartheta_\Omega`$.

### 1.2 Native codes: pair blocks, and $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$

Notation of [SHIFT2.md](SHIFT2.md) §3.2 (cn is the chain number). For a stage $`T \lt \omega^\omega`$, the **stage primitive** is $`f^T_j = \vartheta^{j+1}_{Q^T_{j+1}}`$, where $`Q^T_j`$ is the supremum of the end points
of the stages below $`T`$. $`\Xi[k]`$ is the end point (below $`\Omega_2`$) of the stages $`T \lt \omega^{k+1}`$, $`\Xi[\omega] = \sup_k \Xi[k]`$, and $`Z[k]`$ is the least fixed point of $`\theta_{\Xi[k]}`$.

- **The minor points of the twentieth-round review are applied** (**2 reviews**): the closure of the normal-form template is a definition and the "transfers" are remarks; the
  checked evidence for one atom code is for a variant of the shape in the proof; the chains inside a module chain stay inside it; wording points.
- **Stage systems** (proved): for every stage $`T \lt \omega^\omega`$ and every $`n`$, the stage-$`T`$ system of terms, with unique finite terms and the comparison rule for primitives.
  (The referee: one part, "only primitives of type below $`T`$ at any depth", is false as worded if the leaves count, and true in the form the proofs use.)
- **Pair blocks** (proved). The item $`\langle f^T_j(\beta)\rangle`$ of a row is realized by $`g \lt a \lt b \lt d_1 \lt \dots \lt d_k`$ with $`a \lt_2 b`$, $`a \le_1 \tau(T)`$ and $`g \le_1 \tau(T) + g + V_j(\beta)`$, where
  $`\tau(T) = d_k\cdot c_k + \dots + d_1\cdot c_1 + b\cdot c_0`$ for $`T = \omega^k\cdot c_k + \dots + c_0`$: the bare pair carries the endless descent of levels, the free levels $`d`$ carry the stage, and the head $`g`$
  carries the argument. Every code is an RF fan-free pattern with $`\mathrm{cn} \le 2`$, also with several pair blocks side by side (SHAPE$`^p`$).
- **The copy rule** (ROW$`^p_j`$ with all 9 cases, INNER-PAIR, TOP-MAKE$`^p_j`$; proved). A new pair block is always a copy: in a comparison, by R1 at a head that reaches over a pair block of
  large enough type; in a top, by R1 at a root of one pair $`a \lt_2 b`$ whose left end reaches past $`b`$. So one top pair with $`a \le_1 b\cdot 2`$ hosts everything, and no top with two pairs side
  by side is needed. (The referee: the hypothesis of TOP-MAKE$`^p_j`$ must be narrowed to the parts it realizes, and "depth" must be defined, or one more root taken.)
- **Theorem IDX$`^p`$** (proved). Natively, $`\iota(\mathrm{CH}_3) \ge Z[k]`$ for every $`k`$, so $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0) = \sup_k Z[k]`$. The case $`T = 1`$ is the atom item for indices $`\ge P + 1`$ and the same item
  at every higher cardinal, both open in [SHIFT2.md](SHIFT2.md) §3.2.
- **TOP$`^3`$, Theorem IDX$`^3`$** (proved). A top with a second pair above $`b`$ ($`\mathrm{cn} = 3`$) hosts every code of every stage, so natively $`\iota(\mathrm{CH}_4) \ge Z^{(3)}`$, the least fixed point of
  $`\theta_{\Xi[\omega]}`$. (The referee: correct, but $`Z^{(3)}`$ is only the next fixed point.)
- Conjectured names: $`\Xi[\omega] = \psi_{\Omega_2}(\Omega_\omega\cdot\omega^\omega)`$ and $`\theta_{\Xi[\omega]}(0) = H(\Xi[\omega])`$.
- **What this adds** (the referee's point on the program, not a defect of the paper): as ordinal bounds, all of §1.2 already follows from the known
  $`\iota(\mathrm{CH}_3) \gt \iota(\mathrm{CH}_2) \gt \nu_C \ge X_{11}`$; its value is that the codes are native module systems for RED-TOWER. By a remark that rests on a conjectured dictionary,
  every index system below $`\Omega_2`$ (any chain number) stays below $`\upsilon^* \lt \theta_0`$, so reaching $`\theta_0`$ needs index systems above that level.
- **Open**: stages $`T \ge \omega^\omega`$ (outline, with $`\mathrm{cn} = 3`$); uncountable stage indices (the copy rule needs a gap above the code of the smaller stage, which an index below
  $`\Omega_2`$ cannot give in this block format; no impossibility is proved); $`\Omega_{\omega+1}`$ and $`\Omega_{\omega\cdot 2}`$ (conjecture: the chain number must grow, so RED-TOWER is the frame).

### 1.3 The shapes of $`\Phi_3`$: 3,113 of 3,166

Notation of [SHIFT2.md](SHIFT2.md) §3.3.

- **The minor points of the twentieth-round review are applied** (**2 reviews**): BIN-F is restated with the two facts it used (BIN-F′), the three points of BIN-INS are made exact, and
  the programs of this round are kept with checksums.
- **M5 for every $`n`$** (13; proved, checked line by line against the program). **FAM-B**: the witness members of the program, indexed by their place $`\sigma`$ in the binomial tree, have every
  program value (reach, successor, witness, anchor, copies, records) given by one formula in $`\sigma`$. **SKEL-F1** (a fixed head, decided by a finite computation) and **SKEL-F2** (a head that
  depends on $`n`$) give the rest of $`\mathrm{conv}(A[n])`$. So **BIN-SHAPE holds for every $`n`$** (BIN-ALL), and with M5-DER all 13 are proved.
- **$`t = 2`$, shapes** (proved). For 55 matrices the bad part is one column, so the term of $`A[n]`$ has one chain marker (INPUT-CH). **FAM-D**: the members of the D-chain all have the
  same reach. **CHN-OPQ**: the unchanged program, run on terms with chain markers through five hooks (each a lemma) and a word comparison that is exact or else stops, gives
  $`\mathrm{conv}(A[n])`$ for every $`n \ge 5`$, for all 55. (The referee: proved for these 55 runs and the core used below; as a general theorem the markers need a normal form.)
- **$`t = 2`$, derivations** (proved). **TRANSFER-D**: a BASE-PHI-R solution whose chain block is the D-chain stays a solution when the chain grows by one member. This proves 25 matrices
  (all 24 whose head of the top chain moves, and one more of class III). **BASE-PHI-R′** (the letter $`x`$ may lie in the final segment) and **SUM-CORE-CH** add 4 of class SUM.
- **The tally** (checked; $`3{,}113 = 3{,}071 + 13 + 25 + 4`$):

| class | matrices | proved for every $`n`$ | given a condition checked for small $`n`$ | open |
|---|---|---|---|---|
| I | 581 | 573 | 0 | 8 |
| SUM | 603 | 586 | 1 | 16 |
| ROOT | 635 | 634 | 0 | 1 |
| III | 1,347 | 1,320 | 0 | 27 |
| all | 3,166 | 3,113 | 1 | 52 |

- **Left** (53): $`t = 1`$: 3 of class III with no shape (the input grows by a vertical chain with a constant label); $`t = 2`$ with the shape proved but no derivation: 26 (I 8, SUM 7,
  III 11; 21 have the D-chain below the point, 5 have no BASE-PHI-R solution); $`t = 2`$ with no shape: 24 (III 13, SUM 10, ROOT 1; they need a marker for staircases).
- The referee's minor points: the equality rule and the hashes of chain markers need a normal form (no such case occurs in the 56 runs); one corner of the word comparison is
  correct only because of a sample inside it, so that sample is part of the method; $`\mathrm{conv}`$ means the closure without the program's size guard; two wording points.

### 1.4 $`\nu_C = \nu_S`$: reaches that commute with base change, under LOW

Notation of [SHIFT2.md](SHIFT2.md) §3.4. **LOW** is the hypothesis $`\nu_C \le \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, and **LOW$`_x`$** is $`x \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ for the pair $`(x, \nu)`$. TC⁺ is the statement
that the reaches of restarts commute with base change.

- **Reading of the papers** (cited, correct). [W07a] L.7.9, 7.10, 8.1, 8.2 and Carlson–Wilken 2012, L.3.2, 3.7, 3.8, 3.11 are equivariance statements, all proved from [W07a] L.7.9. Their
  translation into $`R_2^+`$ is an analogy (a remark, not a proved statement).
- **DOMAIN** (proved). Every tool that uses the η-form (GEN⁺, D′-UNC, EXACT-O, EXACT-LONG, the transports, R-CAP) concerns only points below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. So these tools
  reach the pair $`(x, \nu)`$ only under LOW or LOW$`_x`$. Under the conjectured names of the fan program ($`u_0 = \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, $`x = L(\omega)`$, $`\nu = L(\omega+1)`$), LOW$`_x`$ is
  false, and then no result of the η-form applies to $`(x, \nu)`$. Under LOW: LOW-FACTS (proved).
- **Conditional results, not counted.** The referee found these correct as conditional results (FRAG where stated), but raised a **blocking point**: all of them assume LOW or
  LOW$`_x`$, which is not proved and which the conjectured names make false. They are: UNIF-OMEGA2 and the η-base changes for every η-offset below $`\theta`$, so (U1) past every index fixed
  point; TC$`^+_\Psi`$ for short restarts with $`\tau \le \Phi^\chi_\Omega + 1`$; MULTI-FAR$`_k`$ and room below $`\theta`$ ("room below $`\mathbb{G}^\chi`$" is empty, since the maps are defined only below $`\theta`$);
  TOP-REG$`^{\Psi+}`$; PLACE-Ψ (after a repair of one choice of base) and RES-ALL$`^\Psi`$; an η-zone system with $`c_x \gt x^\#`$. The inspection after TWIST is an outline.
- **Not proved** (blocking point): TC⁺ for long restarts. The paper's long case assumes a code transport, which for block and zone maps needs η-offsets $`\ge G_2 \gt \theta`$. So (U3) for long
  interior restarts, and every span that contains one, stay open.
- **Open**: $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$. Missing: exact caps that commute with base change for short restarts with code in $`[\Phi^\chi_\Omega + 2, \theta)`$; offsets $`\ge \theta`$ with long
  interior restarts; and, if LOW fails, an η-form relative to a point above $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (conjecture REL-ETA). This paper uses the caps of [SHIFT2.md](SHIFT2.md) §3.1, not
  those of §1.1.

### 1.5 Status after the twenty-first round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{13}]`$ given FRAG ($`[0, X_9]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$.
  No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 3,113 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z_\omega`$, $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$ and
  $`\iota(\mathrm{CH}_4) \ge Z^{(3)}`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: left: (D1b) and (E4); every η-form tool needs LOW, which is open.

### 1.6 Checks of the twenty-first round

Each run was under 60 seconds; none is a proof.

- §1.1. Names, normal forms, $`D'`$, the literal form of $`X_{13}`$ and $`X_{12} \lt X_{13} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$: Python and Lean agree (the Lean file only compares terms; green, and green in the
  referee's rerun). 40 predictions of PSI2-θ past $`\Omega_2^{\Phi^\chi_\Omega}`$, stops included (all as predicted); 300 random normal forms $`\psi_{\Omega_2}(\beta)`$ (every component below the value,
  monotone on all pairs); the level shift on 240 terms (0 order mismatches). The referee: T1~ with CONV predicts the order of InaccPsi on 3 × 14,280 random pairs (0 mismatches); CNST on
  300 codes and 9 $`\varepsilon`$-numbers (0 mismatches); 8 new boundary predictions, all as predicted.
- §1.2. All 24 blocks are patterns, RF and fan-free with the stated chain number. Certificates, all replayed: 27 of 27 in the predicted direction, 0 of 12 in the reverse direction,
  and 11 of 11 extra ones (among them $`\mathrm{TOP}^3(0) \lt \mathrm{CH}_3 \lt \mathrm{TOP}^3(1)`$). The referee: the block program rerun gives the same output; 2 new predicted certificates found, none of
  8 reverse ones.
- §1.3. The paper: the predicted $`\mathrm{conv}(A[n])`$ equals the program's for $`n = 0, \dots, 9`$ (130 builds), and the instances of CHN-OPQ for $`n = 5, \dots, 8`$ (220 builds). The referee: the family
  values at $`N = 12, 25, 50, 100`$; the predicted $`\mathrm{conv}`$ at $`n = 10`$ for all 13 M5 (up to 6,151 nodes) and at $`n = 12`$ for 7; the 55 templates at $`n = 15`$ and $`n = 30`$; the transferred
  data at $`n = 12`$ and $`n = 20`$. No counterexample.
- §1.4. The paper: the order of the bounds of the tiers, $`D'`$ at two long bases, controls, and UNIF-OMEGA2 on 2 × 14,280 pairs (0 mismatches). The referee: UNIF-OMEGA2 with atoms in more
  places on 2 × 9,900 pairs (0 mismatches; a control map fails only outside the hypothesis), a base change over two levels on 58 offsets (0 failures), and a Lean file for the
  order of the bounds (green).

### 1.7 Open

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$; (P) needs the caps listed in §1.1, and (Q′) the isominimal patterns of $`L(\omega)`$; bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$,
  $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{13}`$ given FRAG: PSI-n (the counting rule over two levels) and the $`n`$-ary tier up to $`\theta`$, then codes in $`[\theta, G_2)`$.
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ or, by RED-TOWER, through native codes with a growing chain number; these now need index systems above
  $`\Omega_2`$ (next inside the present one: stages $`\ge \omega^\omega`$ and uncountable stage indices); UNIF-FS below SRO on the 53 matrices of §1.3.
- $`\nu_C = \nu_S`$: LOW (or an η-form above $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$), TC⁺ for long restarts, (D1b) and (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long restarts with $`D \ge \Phi^\vartheta_\Omega`$ or $`m_0 \ge \Phi^\vartheta_\Omega`$; names beyond
  $`X_{13}`$; the rest of [COVER.md](COVER.md) §9.
