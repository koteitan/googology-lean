[← Back](README.md) | [English](SHIFT3.md) | [Japanese](SHIFT3-ja.md)

# $`R_2^+`$, the twenty-first and twenty-second rounds: $`\nu_C \ge X_{14}`$ given FRAG, the hierarchies $`\vartheta_D`$ and the counting rule PSI-n, pair blocks, the shapes of $`\Phi_3`$, and LOW

This page continues [SHIFT2.md](SHIFT2.md) (§3 there is the twentieth round); §1 is the twenty-first round and §2 the twenty-second. The twenty-third and twenty-fourth rounds are on [SHIFT4.md](SHIFT4.md), the twenty-fifth and twenty-sixth on [SHIFT5.md](SHIFT5.md), the twenty-seventh to twenty-ninth on [SHIFT6.md](SHIFT6.md), the thirtieth on [SHIFT7.md](SHIFT7.md). The status words are those of [README.md](README.md) §3: **proved** means that
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
  UNIF-θ needs an additive map. Both are repaired in §2.1, with 2 reviews.)
- **Wilken's side** (proved; it uses only [W07a] L.3.30, L.4.2–4.4 and Thm 3.23). Let $`\tau`$ be $`1`$ or a $`\upsilon`$-point. Every $`\varepsilon`$-number $`\alpha \in (\tau, \tau^\infty)`$ is
  $`\theta^\tau(\Omega_1\cdot(1+E_\alpha) + \eta)`$, and for every index $`E \le \varepsilon_{\Omega_1+1}`$ with $`K(E) \subset \alpha`$: $`\alpha \in C^{\Omega_1}_E`$ iff $`E_\alpha \ge E`$ (**VEB-THETA$`^\vartheta`$**), and
  $`\theta^\tau(\Omega_1\cdot(1+E) + \eta) = \mathrm{ex}^\tau_E(\eta)`$ (**EXACT-LEVEL$`^\vartheta`$**). So Wilken's terms and the forms are the same terms. Wilken's relativized Bachmann–Howard point
  $`\theta^\tau(\varepsilon_{\Omega_1+1})`$ is the least element of $`C^{\Omega_1}_{\varepsilon_{\Omega_1+1}}`$ above $`\tau`$, and every $`\upsilon`$-point lies in $`C^{\Omega_1}_{\varepsilon_{\Omega_1+1}}`$. (The referee: one citation of
  [W07a] L.4.3 for $`\theta_1`$, where the paper states it only for $`\theta^\tau`$, needs a one-line repair from L.4.2 and L.3.30. Repaired in §2.1, with 2 reviews.)
- **Base change** (EXACT-θ, proved). Wilken's base change from one $`\upsilon`$-point to a smaller one sends the value of every form at the first point to its value at the second, also with a
  parameter map. No fixed-point lemma is needed. (The referee: the parameters of a reading also contain the exponents of constant coefficients; harmless, stated in §2.1.)
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
  as a substitution, is false as written; it must be the full shift $`\Omega_k \mapsto \Omega_{k-1}`$; it is not used elsewhere. The full shift is now proved, LEVEL-SHIFT, §2.1.)
- **Theorem X13** (proved, given FRAG). As X12, with R-CAP$`^\vartheta`$ and CEIL$`^\vartheta`$:

```math
\nu_C \ge X_{13} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Phi^\vartheta_2} + \omega^{\mathbb{G}^\vartheta+1} + \omega^{G_2+1}),\qquad \Phi^\vartheta_2 = \psi_{\Omega_3}(\varepsilon_{\Omega_3+1}).
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{13}]`$, both halves, given FRAG**, and $`X_{12} \lt X_{13} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. Without FRAG the range stays $`[0, X_4]`$. Also
(P-LOW$`^\vartheta`$) every restart $`a`$ with (P) has $`e_a \ge \mathbb{G}^\vartheta + 1`$.

- **Not proved** (open, as the paper says): (P) and (Q′) at $`(L(\omega), L(\omega+1))`$ or at any named pair, and so an InaccPsi upper bound for $`\nu_C`$. Missing: exact caps for short restarts
  with $`\tau \in (\Phi^\vartheta_\Omega + 1, G_2)`$, and for long restarts with $`D \ge \Phi^\vartheta_\Omega`$ or $`m_0 \ge \Phi^\vartheta_\Omega`$ (for codes $`\ge \mathbb{G}^\vartheta`$, where the predecessors in (P) now are, there is
  no upper bound at all); η-offsets at or above $`\Phi^\vartheta_\Omega`$, multipliers at or above $`\Phi^\vartheta_2`$. Each tier moves the predecessors in (P) just above its own cap region.
- **Next** (done in §2.1: PSI-n, and the range $`X_{14}`$ below). The tier of $`n`$-ary hierarchies up to $`\theta`$: Wilken's side and base change go level by level (outline); the InaccPsi side, **PSI-n**, is open. In Buchholz's hull
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
  In the clause "only primitives of type below $`T`$ at any depth", only the parts of the term at the levels $`\ge j`$ count, not the leaves below them (the referee: with the leaves
  counted the clause is false; the proofs use only this form).
- **Pair blocks** (proved). The item $`\langle f^T_j(\beta)\rangle`$ of a row is realized by $`g \lt a \lt b \lt d_1 \lt \dots \lt d_k`$ with $`a \lt_2 b`$, $`a \le_1 \tau(T)`$ and $`g \le_1 \tau(T) + g + V_j(\beta)`$, where
  $`\tau(T) = d_k\cdot c_k + \dots + d_1\cdot c_1 + b\cdot c_0`$ for $`T = \omega^k\cdot c_k + \dots + c_0`$: the bare pair carries the endless descent of levels, the free levels $`d`$ carry the stage, and the head $`g`$
  carries the argument. Every code is an RF fan-free pattern with $`\mathrm{cn} \le 2`$, also with several pair blocks side by side (SHAPE$`^p`$).
- **The copy rule** (ROW$`^p_j`$ with all 9 cases, INNER-PAIR, TOP-MAKE$`^p_j`$; proved). A new pair block is always a copy: in a comparison, by R1 at a head that reaches over a pair block of
  large enough type; in a top, by R1 at a root of one pair $`a \lt_2 b`$ whose left end reaches past $`b`$. So one top pair with $`a \le_1 b\cdot 2`$ hosts everything, and no top with two pairs side
  by side is needed. The hypothesis of TOP-MAKE$`^p_j`$ is read only for the parts it realizes, and one more R3-root is taken where a depth would be needed (such a root is
  always available), as the referee asked.
- **Theorem IDX$`^p`$** (proved). Natively, $`\iota(\mathrm{CH}_3) \ge Z[k]`$ for every $`k`$, so $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0) = \sup_k Z[k]`$. The case $`T = 1`$ is the atom item for indices $`\ge P + 1`$ and the same item
  at every higher cardinal, both open in [SHIFT2.md](SHIFT2.md) §3.2.
- **TOP$`^3`$, Theorem IDX$`^3`$** (proved). A top with a second pair above $`b`$ ($`\mathrm{cn} = 3`$) hosts every code of every stage, so natively $`\iota(\mathrm{CH}_4) \ge Z^{(3)}`$, the least fixed point of
  $`\theta_{\Xi[\omega]}`$. (The referee: correct, but $`Z^{(3)}`$ is only the next fixed point.)
- Conjectured names: $`\Xi[\omega] = \psi_{\Omega_2}(\Omega_\omega\cdot\omega^\omega)`$ and $`\theta_{\Xi[\omega]}(0) = H(\Xi[\omega])`$. (The twenty-fourth round proves the first and refutes the second, [SHIFT4.md](SHIFT4.md) §2.4.)
- **What this adds** (the referee's point on the program, not a defect of the paper): as ordinal bounds, all of §1.2 already follows from the known
  $`\iota(\mathrm{CH}_3) \gt \iota(\mathrm{CH}_2) \gt \nu_C \ge X_{11}`$; its value is that the codes are native module systems for RED-TOWER. By a remark that rests on a conjectured dictionary,
  every index system below $`\Omega_2`$ (any chain number) stays below $`\upsilon^* \lt \theta_0`$, so reaching $`\theta_0`$ needs index systems above that level. (The twenty-second round shows that the
  argument of this remark fails, so the statement is open; also the level of the indices does not matter, §2.2; the twenty-third round gives a native bound past $`\upsilon^*`$, [SHIFT4.md](SHIFT4.md) §1.2; the twenty-ninth round shows that systems with indices below $`\Omega_2`$ go far past $`\upsilon^*`$, so the remark is superseded, [SHIFT6.md](SHIFT6.md) §3.3.)
- **Open**: stages $`T \ge \omega^\omega`$ (outline, with $`\mathrm{cn} = 3`$); uncountable stage indices (the copy rule needs a gap above the code of the smaller stage, which an index below
  $`\Omega_2`$ cannot give in this block format; no impossibility is proved; the twenty-ninth round removes this gap by reflecting the pair at its own left end first, [SHIFT6.md](SHIFT6.md) §3.3); $`\Omega_{\omega+1}`$ and $`\Omega_{\omega\cdot 2}`$ (conjecture: the chain number must grow, so RED-TOWER is the frame).

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
  (Applied in §2.3, with 2 reviews.)

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
  (The referee's other minor points, on the hypotheses of the η-base changes and one overstated status sentence, are used in their corrected form in §2.4.)
- **Not proved** (blocking point): TC⁺ for long restarts. The paper's long case assumes a code transport, which for block and zone maps needs η-offsets $`\ge G_2 \gt \theta`$. So (U3) for long
  interior restarts, and every span that contains one, stay open.
- **Open**: $`\nu_C = \nu_S`$ and $`\nu_C \lt \nu_S`$. Missing: exact caps that commute with base change for short restarts with code in $`[\Phi^\chi_\Omega + 2, \theta)`$; offsets $`\ge \theta`$ with long
  interior restarts; and, if LOW fails, an η-form relative to a point above $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (conjecture REL-ETA; replaced by the global η-form in §2.4). This paper uses the caps of [SHIFT2.md](SHIFT2.md) §3.1, not
  those of §1.1.

### 1.5 Status after the twenty-first round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{13}]`$ given FRAG ($`[0, X_9]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$.
  No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 3,113 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z_\omega`$, $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$ and
  $`\iota(\mathrm{CH}_4) \ge Z^{(3)}`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: left: (D1b) and (E4); every η-form tool needs LOW, which is open.

The twenty-second to thirtieth rounds changed this status; see §2.5, [SHIFT4.md](SHIFT4.md) §1.5, §2.5, [SHIFT5.md](SHIFT5.md) §1.4, §2.4, [SHIFT6.md](SHIFT6.md) §1.4, §2.4, §3.4 and [SHIFT7.md](SHIFT7.md) §1.4.

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

The twenty-second to thirtieth rounds changed this list; the current list is [SHIFT7.md](SHIFT7.md) §1.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$; (P) needs the caps listed in §1.1, and (Q′) the isominimal patterns of $`L(\omega)`$; bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$,
  $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{13}`$ given FRAG: PSI-n (the counting rule over two levels) and the $`n`$-ary tier up to $`\theta`$, then codes in $`[\theta, G_2)`$.
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ or, by RED-TOWER, through native codes with a growing chain number; these now need index systems above
  $`\Omega_2`$ (next inside the present one: stages $`\ge \omega^\omega`$ and uncountable stage indices); UNIF-FS below SRO on the 53 matrices of §1.3.
- $`\nu_C = \nu_S`$: LOW (or an η-form above $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$), TC⁺ for long restarts, (D1b) and (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long restarts with $`D \ge \Phi^\vartheta_\Omega`$ or $`m_0 \ge \Phi^\vartheta_\Omega`$; names beyond
  $`X_{13}`$; the rest of [COVER.md](COVER.md) §9.

## 2. The twenty-second round

Four papers (2026-10). The papers of §2.1 and §2.3 were refereed once. The paper of §2.4 was refereed twice: a second referee checked the revised file and derived
its proofs again, so a result of §2.4 has **2 reviews**. The paper of §2.2 was refereed once, revised, and refereed again; the second referee checked the new part and the
repairs but did not derive the old part again, so a result of §2.2 has 1 review. **2 reviews** on a repaired statement means that a referee of the twenty-first round
proposed the repair and a referee of this round checked it as written out. None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006),
or the equivalence that Carlson 2009, p. 97, announces. Papers cited here: [W07a] (Def 3.1, Thm 3.23, Def 3.28, L.3.30, L.4.2–4.4, Def 5.1, L.5.3); Wilken,
"Σ₁-elementarity and Skolem hull operators", APAL 145 (2007), Cor 5.10. No Lean file was added: two papers (§2.1, §2.4) checked a Lean file that only compares terms
(`#eval`, no theorem; green, and green in the referees' reruns), so these count as checks. The minor points of the twenty-first-round reviews are applied in §1 and below.
Levels are numbered as in [SHIFT.md](SHIFT.md) (one higher than in the papers).

### 2.1 The counting rule PSI-n and the tier up to θ: $`\nu_C \ge X_{14}`$ given FRAG

Notation of §1.1; $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$ as in [SHIFT2.md](SHIFT2.md) §2.1. New name:

```math
X_{14} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2\cdot 2} + \omega^{G(\theta_2)+1} + \omega^{G_2+1}),\qquad G(\theta_2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2\cdot 2}).
```

- **The minor points of the twenty-first-round review are applied** (proved, **2 reviews**). The citation of [W07a] L.4.3 for $`\theta_1`$ is replaced by L.3.30 and L.4.2.
  The fixed-point side condition of UNIF-θ is proved for regular cardinals. The maps that move constants are additive wherever additivity is used. The parameters of a
  reading also contain the exponents of constant coefficients. The level reading is the full shift $`\mathrm{Sh}`$ ($`\Omega_k \mapsto \Omega_{k-1}`$, $`\psi_{\Omega_k} \mapsto \psi_{\Omega_{k-1}}`$), now a proposition
  (LEVEL-SHIFT). Two wording points. (The referee of this round: one clause of the repair holds only inside Wilken's system $`T_1`$; the needed fact follows in one line.)
- **The hierarchies for every $`n`$** (proved). For $`n \ge 2`$ the system of the $`C^{\Omega_j}_D`$, $`2 \le j \le n`$, where the constants of an index are read through the exact-level
  pair of each strongly critical atom. CLUB, normal forms, LEVEL and T1~ hold at every unit. The forms TmTh$`^n`$ are unique, cover $`[0, \psi_{\Omega_2}(\varepsilon_{\Omega_n+1}))`$, and
  are decided alike at every tuple of units (UNIF$`^n`$). The $`n`$-system is the restriction of the $`(n+1)`$-system (AGREE$`^n`$).
- **Theorem PSI-n** (proved; the referee derived all three steps again). For $`2 \le j \le n`$ every normal form $`\psi_{\Omega_j}(\beta)`$ with $`\beta \lt \varepsilon_{\Omega_n+1}`$ is given by one
  counting rule. Write $`\beta = H + \delta`$, where $`H`$ is the sum of the Cantor normal form summands $`\ge \Omega_{j+1}`$. If $`H \gt 0`$, the rule starts at the **high base**, the least
  element of $`C^{\Omega_j}_{\psi_{\Omega_{j+1}}(H)}`$ above the constants of $`\psi_{\Omega_{j+1}}(H)`$; then $`\delta`$ is counted as in PSI2-θ (§1.1). So the "parameter lag" of §1.1 is exactly the
  index $`\psi_{\Omega_{j+1}}(H)`$ of the high base. Example: $`\psi_{\Omega_2}(\Omega_3)`$ is the least element of $`C^{\Omega_2}_{\psi_{\Omega_3}(\Omega_3)}`$ above $`\Omega_1`$. Proof: downward induction on $`j`$, then on $`\beta`$,
  in three steps (no stop for a normal form; every smaller normal form has a smaller value; every value below is reached). Consequences: $`\psi_{\Omega_2}(\varepsilon_{\Omega_n+1})`$ is the
  end point of the $`n`$-system, and, by Lemma CONT for every $`\psi_\kappa`$, $`\sup_n \psi_{\Omega_2}(\varepsilon_{\Omega_n+1}) = \theta`$ and $`\sup_n \psi_{\Omega_3}(\varepsilon_{\Omega_n+1}) = \theta_2`$. Whether the end points
  $`\Xi_n`$ of the native codes of [SHIFT2.md](SHIFT2.md) §2.2 are the same ordinals is not proved and not used (the twenty-third round proves it, [SHIFT4.md](SHIFT4.md) §1.2). (The referee: two steps are asserted and need a short argument
  each, a comparison with high bases above $`\beta`$ and an induction on the size of terms. Applied in [SHIFT4.md](SHIFT4.md) §1.1, with 2 reviews.)
- **CNST$`^n`$** (proved). The constants of the form of an ordinal are below a threshold exactly when the maximal subterms of its InaccPsi term below the unit are. So
  the hull lemma (R4) holds for every code below $`\theta`$, and for multipliers below $`\theta_2`$.
- **Wilken's side** (proved after a change of citation). [W07a] L.4.3 and L.4.4 hold at every level $`\theta_m`$; VEB-THETA$`^n`$ and EXACT-LEVEL$`^n`$ hold; base change is the identity on
  forms. (The referee: "every element of $`T^\tau`$ below $`\Omega_{m+1}`$ lies in an initial segment" is false for $`m \ge 1`$, since $`T^\tau`$ is countable; the proofs run in Wilken's
  system with $`\tau := \Omega_m`$, [W07a] Def 3.1, Thm 3.23, which contains $`T^\tau`$.)
- **The tier up to θ** (proved, given FRAG, as a list of substitutions into §1.1). **EXACT-O$`^n`$**: every restart $`\nu`$ with $`\rho_{\nu+\omega^2} \le \nu_S`$ and $`\tau_\nu \lt \theta`$ has
  $`r(\nu) = \delta_\nu + o_\nu(\tau_\nu)`$. EXACT-LONG and CROSS-O for $`D, m_0 \lt \theta`$; η-offsets below $`\theta`$; multipliers below $`\theta_2`$; **R-CAP$`^\theta`$** for every code $`G_2 \le m \lt G(\theta_2)`$;
  CROSS-SHARP up to the multiplier $`\theta_2`$; CEIL$`^\theta`$ (no FRAG).
- **Theorem X14** (proved, given FRAG). As X13, with R-CAP$`^\theta`$ and CEIL$`^\theta`$: $`\nu_C \ge X_{14}`$. So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_{14}]`$, both halves, given FRAG**,
  and $`X_{13} \lt X_{14} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. This was the conjecture of §1.1. Also (P-LOW$`^\theta`$) every restart $`a`$ with (P) has $`e_a \ge G(\theta_2) + 1`$.
- **Codes in $`[\theta, G_2)`$** (proved). PSI-θ: $`\theta = \mathrm{ex}^{\Omega_1}_{\theta_2}(0)`$ and $`G(\zeta) = \mathrm{ex}^{\Omega_1}_{\theta_2}(\zeta)`$ (the index $`\theta_2`$ at the unit $`\Omega_2`$). Above $`\pi_g`$ the hull lemma takes
  the form (R4′): $`\tau \in C_g`$ iff $`K_\tau \subset H(g)`$ and $`\tau \lt \pi_g`$. Given FRAG: EXACT-O$`^\theta`$ for $`\tau_\nu \lt G(\omega+1)\cdot\omega`$, where the target stays in the window of TOP-REG⁺,
  and the lower bound $`r(\nu) \ge \delta_\nu + o_\nu(\tau_\nu)`$ for every $`\tau_\nu \lt G_2`$ (LB$`^\theta`$). (The referee: the reading is onto only below $`\pi_{\eta_\nu}`$, and in the upper bound the reading
  at a smaller restart must be taken from the forms; the fact $`\upsilon_{a+1} = \upsilon_a^\infty`$ is Wilken 2007, APAL 145, Cor 5.10. Applied in [SHIFT4.md](SHIFT4.md) §1.1.)
- **Not proved** (open, as the paper says): the upper bound for $`\tau_\nu \in [G(\omega+1)\cdot\omega, G_2)`$ (the missing lemma is the upper-bound rule TOP-REG for targets $`y \ge \delta_1\cdot\omega`$; the twenty-third round shows that this rule is false as stated, proves its corrected form, and gets exact reaches up to $`\varphi(\omega, G(\omega+1)+1)`$, [SHIFT4.md](SHIFT4.md) §1.1); long
  restarts with $`D \ge \theta`$ or $`m_0 \ge \theta`$; η-offsets $`\ge \theta`$; multipliers $`\ge \theta_2`$; (P) and (Q′) at a named pair, and so an InaccPsi upper bound for $`\nu_C`$. P-LOW$`^\theta`$ puts the
  predecessors in (P) past every cap of this round.

### 2.2 Native codes: an InaccPsi name for a native bound

Notation of §1.2 and [SHIFT.md](SHIFT.md) §9.2. An index system is a well-ordered set of indices, each with a finite set $`K`$ of countable parameters; it defines the functions
$`\theta_\Delta`$ as in [SHIFT.md](SHIFT.md) §9.2. $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`D`$ is the set of $`\eta \lt \Omega_2`$ that give a normal form, and $`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$.

- **The first review** found one blocking point: a conjectured dictionary of the paper beyond $`Z`$ is false. It is withdrawn and not recorded here. The other points are applied.
- **INV, FIN-K, EMB-W** (proved). The functions $`\theta_\Delta`$ depend only on the well-order of the indices with their parameter sets (finite parameters do not matter), and every
  index system is isomorphic to one whose indices are ordinals below $`\Omega_2`$. So the level of the indices is invisible: an index system at $`\Omega_2`$ is a relabelled one at
  $`\Omega_1`$, and its bound is below a known one (LEVEL-2, no new bound).
- **FLAT, INCONS** (proved). $`H(\eta) = \upsilon^*`$ for every $`\eta \in [Z, \Omega_2]`$. So the remark of §1.2 ("every index system below $`\Omega_2`$ stays below $`\upsilon^*`$"), whose argument used a
  conjectured dictionary together with conjectured names, rests on a contradiction; the argument fails, and the statement is open.
- **RED-DICT, GREEDY-EMB** (proved). If $`f`$ maps $`D \cap X`$ strictly increasingly into the indices with $`K(f(\eta)) \subset H(\eta)`$, then $`H(\eta) \le \theta_{f(\eta)}(0)`$. This hypothesis (EMB) holds iff a greedy
  embedding of one countable ordinal into the index system is total.
- **CNST-ϑ, EMB-2, NAT-2** (proved; new in the revision). Below $`\Phi^\vartheta_\Omega`$ the constants of the forms of §1.1 control the parameters of the hybrid terms of [SHIFT.md](SHIFT.md) §9.2. So
  $`f(\eta) = 1 + \eta`$ satisfies EMB on $`D \cap \Phi^\vartheta_\Omega`$, and natively

```math
\iota(\mathrm{CH}_2) \ge \theta_{\Xi_2}(0) \ge H(\Phi^\vartheta_\Omega) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Phi^\vartheta_\Omega}),\qquad \Phi^\vartheta_\Omega = \psi_{\Omega_2}(\varepsilon_{\Omega_2+1}).
```

This is the first native bound with a proved InaccPsi name. It lies below $`\upsilon^*`$ and below the native $`Z_\omega`$ and the known $`\iota(\mathrm{CH}_2) \gt \nu_C \ge X_{14}`$, so as an ordinal bound it
adds nothing (the referee). $`H(\eta) \le \theta_\eta(0)`$ is the lower half of the dictionary of [SHIFT.md](SHIFT.md) §9.2 only at $`\varepsilon`$-numbers $`\eta`$.

- **Conditional, not counted.** Given EMB for the index system of [SHIFT2.md](SHIFT2.md) §3.2, natively $`\upsilon^* \lt \iota(\mathrm{CH}_3)`$ by a module system past $`\upsilon^*`$ (proved as an implication).
- **Not proved** (blocking point of the second review): the claimed reduction of EMB to the codes in $`[\Phi^\vartheta_\Omega, Z)`$. EMB-2 is proved for the hybrid parameters, the bound needs the pure
  ones, and the two parts must be joined. (Repaired in [SHIFT4.md](SHIFT4.md) §1.2, with 2 reviews: EMB holds on all of $`D`$, and natively $`\upsilon^* \lt \iota(\mathrm{CH}_3)`$.)
- **Open**: a native bound past $`\upsilon^*`$; "the chain number must grow" (no theorem says that a system cannot host a code); stages $`\ge \omega^\omega`$ and uncountable stage indices.

### 2.3 The shapes of $`\Phi_3`$: 3,139 of 3,166

Notation of §1.3.

- **The minor points of the twenty-first-round review are applied** (**2 reviews**). Chain markers have a normal form with an exact equality, and the word comparison tests the
  end of a word first. All 57 templates were run again with the corrected program: the templates are identical, and every instance equals the program's
  $`\mathrm{conv}(A[n])`$ for $`n = 5, \dots, 8`$. So CHN-OPQ holds for these runs with no exception.
- **BASE-PHI-G** (proved, after a one-line repair). One covering of $`\mathrm{conv}(A[n])`$ into any copy of $`\mathrm{conv}(A)`$, built in stages. Against BASE-PHI-R: the chain block may lie anywhere,
  below the point too; its bound $`g`$ need not be a left end (the roots of a left end $`x`$ with $`g \lt x \le`$ the reach of $`g`$ are moved below the copy of $`g`$ by R1); stages may start at any
  one-term node; the point may be a sum. **TRANSFER-G** (proved) carries it from $`n`$ to $`n+1`$ along the D-chain.
- **Theorem T2-G** (proved). All 26 matrices with $`t = 2`$ whose shape was proved but which had no derivation (21 with the D-chain below the point, 5 with no solution of the base rule)
  hold for every $`n`$. (The core $`(0,0,0)(1,1,1)(1,0,0)(2,1,1)`$, which is not in the sample, is proved given one fact that the referee checked.)
- **The tally** (checked; $`3{,}139 = 3{,}113 + 26`$; the one matrix that had a condition checked for small $`n`$ is among the 26):

| class | matrices | proved for every $`n`$ | open |
|---|---|---|---|
| I | 581 | 581 | 0 |
| SUM | 603 | 593 | 10 |
| ROOT | 635 | 634 | 1 |
| III | 1,347 | 1,331 | 16 |
| all | 3,166 | 3,139 | 27 |

- **Left** (27). For all of them the shape of $`\mathrm{conv}(A[n])`$ for every $`n`$ is open: the input does not grow by a chain. 15 (SUM 6, III 9) grow by a staircase of side kids, one node
  per $`n`$; 8 (SUM 4, III 4) by a deep staircase, four nodes per $`n`$; 1 of class ROOT by two interleaved staircases; 3 with $`t = 1`$ by a vertical chain with a constant label. A derivation at
  each $`n \le 4`$ is checked for 16 of the 27. Needed: a marker for staircases, a family lemma for them (outline), a proof of the step with one reflected block (now checked
  level by level), markers for blocks of period 2 or 4, and a marker that refers to itself for $`t = 1`$.
- The referee's minor points: "the image is weakly increasing" is false on sums (the bound needs one line; no accepted solution used the false step); one input fact is cited for
  a core that is not in the earlier files (the referee checked it); the negative probes stop at 20,000 solutions and count that as a failure; one dictionary of the program needs a
  sentence; two section numbers in comments. (Applied in [SHIFT4.md](SHIFT4.md) §1.3, with 2 reviews.)

### 2.4 $`\nu_C = \nu_S`$: the η-form above $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, and LOW (2 reviews)

Notation of §1.4 and [SHIFT.md](SHIFT.md) §1 ($`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$, $`L(\xi) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot\xi)`$). Now $`D`$ is the set of $`\eta \lt \Omega_\omega\cdot\omega`$ with $`\eta \in C_\eta`$,
so the $`H(\eta)`$, $`\eta \in D`$, are all $`\upsilon`$-points below $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ (GEN-EXT, [BREAK.md](BREAK.md) §2). A $`\upsilon`$-point is of level 1 if it is below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2) = H(\Omega_\omega)`$,
and of level 2 if it is in $`[\psi_{\Omega_1}(\Omega_\omega\cdot 2), \psi_{\Omega_1}(\Omega_\omega\cdot 3))`$. A restart $`u`$ is **self-crossing** if $`H(\eta_u + \zeta) \le r(u)`$ for every $`\zeta \lt \omega^{m_u+1}`$ with $`\eta_u + \zeta \in D`$.
**CAP-0** (conjecture): no restart below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ is self-crossing; **CAP-1** (conjecture): no restart of level 2 with code below $`P'`$ is self-crossing. **LOW$`^\omega`$** is $`\nu_C \lt \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$.

- **CODES** (proved). Every restart below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ has code below $`P'`$, and $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ is a restart with code exactly $`P'`$.
- **LOW-RED, SC-SHORT** (proved; the bound $`\mathbb{G}^\vartheta`$ given FRAG). LOW$`_x`$ implies that cofinally many $`u \lt x`$ are self-crossing long restarts with $`\mathbb{G}^\vartheta \le m_u \lt P'`$ (without FRAG:
  $`G_2 \le m_u`$); no restart with code below $`\mathbb{G}^\vartheta`$ is self-crossing. So CAP-0 would refute LOW (proved as an implication).
- **LOW is not decided.** Without hypothesis: either LOW$`_x`$ holds and self-crossing long restarts with codes in $`[\mathbb{G}^\vartheta, P')`$ exist below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$, or
  $`\nu_C \ge Y_1 = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\mathbb{G}^\vartheta+1})`$. (The second referee: there is no evidence for CAP-0 at codes in $`[\mathbb{G}^\vartheta, P')`$, and the pattern of CROSS-SHARP, read past its
  proved range, predicts the opposite. First test case: $`u = \psi_{\Omega_1}(\Omega_\omega + \Omega_3)`$, with code $`\psi_{\Omega_2}(\Omega_\omega + \Omega_3)`$. The twenty-third round decides it: CAP-0 holds at $`u`$, [SHIFT4.md](SHIFT4.md) §1.4.)
- **X13⁺** (proved, given FRAG): $`\nu_C \ge X_{13}^+ = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Phi^\vartheta_2} + \omega^{\mathbb{G}^\vartheta+1}\cdot 2)`$. It is below $`X_{14}`$ of §2.1.
- **The η-form above $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$** (proved). **D-UNC$`^{(2)}`$**: for $`\eta \in D`$ with $`\eta \ge \Omega_\omega`$ and $`\xi \lt P'`$, $`\eta + \xi \in D`$ iff the countable atoms of $`\xi`$ are below
  $`H(\eta + \xi)`$ (the bound grows from $`\theta`$ to $`P'`$). **FIX$`^{(2)}`$, DICT$`^{(2)}`$, T$`^B`$**: Theorem T at the base $`\Omega_\omega\cdot 2`$, $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \theta\cdot\xi) = \upsilon_{\Lambda_1+\xi}`$ for
  countable $`\xi`$ below the first index fixed point $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \theta\cdot\Omega_1)`$, where $`\upsilon_{\Lambda_1} = \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$. **SPLIT**: every $`\upsilon`$-point of level 2 is
  $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e + \theta\cdot\zeta)`$ for exactly one pair $`(e, \zeta)`$ with $`\zeta \lt P'`$. So the points $`L(e)`$ play at level 2 the role that the $`H(e)`$ play at level 1.
- **EXT-ETA** (proved for the tools that are used; the full list is checked only as an inventory). The tools of the η-form of the earlier rounds hold for restarts below
  $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ with $`\eta \in D`$. So the hypothesis LOW of §1.4 can be replaced by LOW$`^\omega`$, which the conjectured names of the fan program satisfy. The conjecture
  REL-ETA of §1.4 is not needed: one clause of it is false, and the global η-form replaces it.
- **TC⁺** (proved, transfer). Short restarts below $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$; long interior restarts with $`D, m_0 \lt \Phi^\vartheta_\Omega`$ at offsets below $`P'`$, for base changes between restarts
  of level 2 with exponent $`\ge P'`$ (the code transport is written out). (D1b): the placement tools hold on $`D`$, and room below $`\mathbb{G}^\vartheta`$ is no longer empty at level 2.
- **Conditional, not counted.** The blocking point of both reviews is about the record: LOW is open, so these results must carry their hypothesis. Under not-LOW:
  $`\nu_C \ge Y_1`$, so the claim holds on $`[0, Y_1]`$ (Theorem X$`^{(2)}`$), and $`r(\psi_{\Omega_1}(\Omega_\omega\cdot 2)) \ge H(\Omega_\omega + \Phi^\vartheta_\Omega)`$. Under CAP-0 and CAP-1 (NU-LOW″): $`x \ge L(\omega)`$, a final segment of
  $`\mathrm{Pred}_1(x)`$ consists of points $`L(e)`$ (when $`x \lt \psi_{\Omega_1}(\Omega_\omega\cdot 3)`$), and $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + \omega^{\mathbb{G}^\vartheta+1})`$; these are the lower halves of the conjectured names $`m_0 = L(0)`$ and $`a_0 = L(\omega)`$.
  At the pair $`(x, \nu)`$, the bases of TC⁺ for long restarts exist only under CAP-1 or the conjectured names.
- **Not proved** (open): LOW; (P) at $`(L(\omega), L(\omega+1))`$, which needs a lower bound for the reaches of restarts of code $`P'`$ across the offset $`\omega^{P'+1}`$ (the level-2 form of "a restart reaches its $`\delta_1`$": the restart $`L(\lambda)`$ reaches $`L(\lambda+\omega+1)`$);
  (P1), the exact caps that commute with base change for codes in $`(\Phi^\vartheta_\Omega + 1, G_2)`$ and for long codes outside EXACT-LONG (the exact caps of §2.1 are not yet shown to commute with
  base change); TC⁺ for long restarts at offsets $`\ge P'`$; $`\nu_C = \nu_S`$.
- The referees' minor points: the summary must not say that REL-ETA holds; the bound $`\xi \lt P'`$ must be stated with TC⁺ for long restarts; the use of CROSS-SHARP at
  $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ should be a lemma of its own; one hypothesis of NU-LOW″ is about $`x`$, not about $`\nu_C`$.

### 2.5 Status after the twenty-second round

The twenty-third to thirtieth rounds changed this status; see [SHIFT4.md](SHIFT4.md) §1.5, §2.5, [SHIFT5.md](SHIFT5.md) §1.4, §2.4, [SHIFT6.md](SHIFT6.md) §1.4, §2.4, §3.4 and [SHIFT7.md](SHIFT7.md) §1.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_{14}]`$ given FRAG ($`[0, X_9]`$ with 2 reviews); the core half holds on $`[0, \nu_C]`$.
  No InaccPsi upper bound for $`\nu_C`$: (P) at a named pair stays open.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 3,139 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z_\omega`$ (and
  $`\iota(\mathrm{CH}_2) \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Phi^\vartheta_\Omega})`$ by a native bound with a proved name), $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$, $`\iota(\mathrm{CH}_4) \ge Z^{(3)}`$. Whether native index systems
  pass $`\upsilon^*`$ is open (the earlier argument against it fails).
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: the tools of the η-form hold below $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$, so LOW is replaced by LOW$`^\omega`$; LOW itself is not decided. Left: (P1), (D1b), (E4).

### 2.6 Checks of the twenty-second round

Each run was under 60 seconds; none is a proof.

- §2.1. The rule against the InaccPsi order on $`5 \times 11{,}990`$, $`2 \times 1{,}598{,}960`$ and $`2 \times 43{,}890`$ ordered pairs (0 mismatches); a wrong rule for the high base gives 63 mismatches.
  Every form with a positive count has its form with count 0 reached (4,844 forms, 0 failures), while three wrong rules fail 223, 182 and 408 times. CNST$`^n`$ on 4,800 tests and
  the level shift on 240 terms and $`2 \times 14{,}280`$ pairs (0 failures). Names, normal forms and $`X_{13} \lt X_{14} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$: Python and Lean agree. The referee: new term pools,
  $`3 \times 14{,}280`$ pairs, 3,401 and 3,351 pairs for two steps of the proof, CNST$`^n`$ at $`\Omega_3`$, and 35,910 pairs of codes in $`[\theta, G_2]`$: no counterexample.
- §2.2. 15 of 15 checks ($`\Phi^\vartheta_\Omega \in D`$, the literal name, $`H(\Phi^\vartheta_\Omega) \lt H(\theta) \lt \upsilon^*`$) and 16 of 16 for FLAT. Certificates, all replayed: 5 of 6 in the predicted direction,
  1 of 2 extra ones, 0 of 5 in the reverse direction. The referee: the reruns give the same output; a check of the supremum in NAT-2 finds no failure.
- §2.3. T2-G for all 27 at $`n = 0, \dots, 5`$, and the moved solution at $`n = 6, 7, 8, 12, 16`$. 0 false successes on 600 random pairs and 318 near pairs. The referee: an independent checker
  accepts all 162 solutions; the templates agree with the program at $`n = 20`$ and $`n = 30`$; 0 wrong successes on 1,134 pairs where the method must fail.
- §2.4. Names, membership in $`D`$ and the order chain (Python and Lean; one inequality in Python only); D-UNC$`^{(2)}`$ on 48 offsets with 6 controls; codes; T$`^B`$ on 12 samples. The
  referees: D-UNC$`^{(2)}`$ on 840 random offsets at 7 bases, SPLIT on 400 points, monotonicity on 9,180 pairs, T$`^B`$ at 4 bases, CODES on 30 more points, the test case of CAP-0
  (memberships and order): 0 disagreements.

### 2.7 Open

The twenty-third to thirtieth rounds changed this list; the current list is [SHIFT7.md](SHIFT7.md) §1.6.

- Upper bounds: (P) and (Q′) at one named pair for $`\nu_C`$. (P) needs the caps of §2.1 and a lower bound at code $`P'`$ (§2.4); (Q′) needs the isominimal patterns of $`L(\omega)`$.
  Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The claim above $`X_{14}`$ given FRAG: the upper-bound rule TOP-REG for targets $`\ge \delta_1\cdot\omega`$; long restarts with $`D \ge \theta`$ or $`m_0 \ge \theta`$; η-offsets $`\ge \theta`$ and multipliers $`\ge \theta_2`$.
- The first inaccessible: a native bound past $`\upsilon^*`$ (EMB for the pure parameters), stages $`\ge \omega^\omega`$, uncountable stage indices, $`\Omega_{\omega+1}`$; UNIF-FS below SRO on the 27
  matrices of §2.3.
- $`\nu_C = \nu_S`$: LOW (CAP-0 at codes in $`[\mathbb{G}^\vartheta, P')`$), LOW$`^\omega`$, (P1), TC⁺ for long restarts at offsets $`\ge P'`$, (D1b), (E4).
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of the long restarts with $`D \ge \theta`$ or $`m_0 \ge \theta`$; names beyond $`X_{14}`$;
  the rest of [COVER.md](COVER.md) §9.
