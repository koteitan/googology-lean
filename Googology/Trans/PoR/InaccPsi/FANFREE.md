[← Back](README.md) | [English](FANFREE.md) | [Japanese](FANFREE-ja.md)

# $`R_2^+`$, the eighth to tenth rounds: the limit jumps, native codes, restart reaches between segments, chains in the fan-free core, the shapes of $`\Phi_3`$, and names past $`\Lambda_\varepsilon`$

This page continues [COVER.md](COVER.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from 2026-10. They
come from three rounds of four papers, the eighth (§1–§6), the ninth (§7–§9) and the tenth (§10–§12); the eleventh round is on the next page, [VEBLEN.md](VEBLEN.md); each paper was refereed once, so a result has 1 review unless a count is given. "2 reviews"
means that two independent papers proved the result and each paper was refereed once. A result marked **outline** was found
"proved (outline)" by its referee; it is not counted as proved. A statement with a blocking point against it is listed under
**Not proved**, even when the rest of its paper is proved. A true statement that its referee found to restate the target, or to
claim more progress than it gives, is listed under **Not counted**. A certificate counts only when it was replayed. As in
[COVER.md](COVER.md) §5–§6, the papers number the levels of nested pairs one lower than these pages; here they are renumbered.
None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009,
p. 97, announces. No result on this page is in Lean, and no Lean file was added. The referees rechecked the Lean files that the
papers use: `TrioCofinal.lean` (`trio_fs`, `trio_cofinal`, behind S-RED of [README.md](README.md) §3), `CountSeg.lean` and `LowSeg.lean`. In the ninth round the referee rebuilt [PSS/Phi.lean](../../BMS/PoR/PSS/Phi.lean) (`ctps_lh`, `stdOrd_lh`, `ctps_anchor`, used in §7.1), with no sorry.

**Notation.** As on [COVER.md](COVER.md). A copy of a pattern $`P`$ is a finite closed set that covers it (Carlson 2009, Def 5.2);
$`P^*`$ is its least realization and $`\iota(P)`$ the point of $`P^*`$. $`S \ll T`$ and the rules R1–R5 are those of [COVER.md](COVER.md) §6.1.
A pattern is RF fan-free if no point has two $`\lt_2`$-successors and no right end is $`\le_1`$ to a larger element. $`m_F`$ is the
least $`\le_1`$-predecessor of the least fan apex $`x_F`$, $`\mathrm{Core}_F = [0, m_F)`$ is the set of points of RF fan-free patterns, $`V_F`$
is the set of $`\le_1`$-predecessors of $`x_F`$, and $`v^+`$ is the next member of $`V_F \cup \{x_F\}`$ above $`v`$. $`H_m`$ is $`m_F \ge \theta_0`$, and
$`H_m \Leftrightarrow FF_{RF}`$ ([COVER.md](COVER.md) §5.3). $`D`$ is the set of countable normal forms without an inaccessible symbol.

## 1. The 26 limit jumps and the fundamental-sequence step

The local step above $`V_3`$ ([README.md](README.md) §6) had 160 neighbour pairs of images of $`G_{B0}`$; 134 were certified, and 26 "limit
jumps" were undecided. Of these, 5 had replayed certificates and LJ2 was proved by hand ([COVER.md](COVER.md) §6.1). A limit jump is an order
statement between two consecutive matrices $`A \lt B`$ with $`B`$ a limit, not a fundamental-sequence step $`\Phi_3(M[n]) \ll \Phi_3(M)`$; by
S-RED the jumps follow from the uniform fundamental-sequence step UNIF-FS, not the other way.

- **The 20 remaining jumps** (proved, 1 review). For each, $`\Phi_3(A) \ll \Phi_3(B)`$, so $`\iota(\Phi_3(A)) \lt \iota(\Phi_3(B))`$. The patterns are
  the output of $`\Phi_3`$ on 40 fixed matrices, so this is a statement about $`\Phi_3`$ itself, with no assumption on shapes. Each
  proof is 3–6 moves of one template: lower the index part (this needs slack, $`p' \lt p`$), lower the upper point to $`c''`$ with
  $`c'' \le_1 c'' + p'`$, nest the inner block, reflect at the root. Four variants by shape (Lemmas JA–JD: 11, 7, 3 and 1 jumps,
  counting LJ1 and LJ2). The referee redid all 20 derivations. So **all 26 limit jumps are settled, none refuted**, and all 160
  neighbour pairs of that sample are in the predicted order.
- **The point relation** (proved, 2 reviews: this paper and the paper of §2 defined it independently). $`S \ll' T`$: every copy of $`T`$
  has a copy of $`S`$ whose point is below the point of the copy of $`T`$; the rest of the copy is free. $`S \ll T`$ implies $`S \ll' T`$, and
  $`S \ll' T`$ implies $`\iota(S) \lt \iota(T)`$; $`\ll'`$ is transitive. This is all that UNIF-FS and S-RED need. One step needs it: for
  A = (0,0,0)(1,1,1)(2,1,1)(2,0,0)(1,0,0)(2,1,1)(3,0,0) the copy of $`\Phi_3(A[n])`$ keeps elements of $`\Phi_3(A)`$ above the point.
- **Eight moves** (proved, 1 review). LOW, REF, NEST, INNER, AP, TOP, BASE and SUB, each an instance of R1–R5, GEN or Carlson 2009,
  L.5.5(7). Every limit step proved so far, in this round and the seventh, is a word in these moves.
- **Two schemas** (proved, 1 review). Lemma IX: if only the index part changes, and the new index part lies below the element it
  refers to, the step holds. Theorem SR*: if the last block refers to its own root, and the block satisfies two conditions (H0), (H1)
  that do not depend on $`n`$, then $`\Phi_3(A[n]) \ll \Phi_3(A)`$ (or $`\ll'`$) for every $`n`$. The referee: some hypotheses of SR* are hidden in a
  definition and should be stated.
- **Families for all $`n`$** (proved for the patterns written out, 1 review). ITER-LOW, SELF-REF, POINT-REF and LONG-K, one limit matrix
  each. For $`\Phi_3`$ this holds given its printed shapes, which are checked for $`n \le 4`$. SR* covers 7 more sampled matrices
  (its conditions shown by naming the moves; checked for $`n \le 5`$).
- **Not proved** (blocking point): IDX-ADD for all $`n`$. The shape claimed for $`n \ge 2`$ is false at $`n = 4`$: the index part of
  $`\Phi_3(A[n])`$ is a chain that grows with $`n`$, and the written step list fails at $`n = 4, 5`$. Proved for $`n \le 3`$; checked for $`n \le 6`$
  with 2–3 more LOW moves. A proof for all $`n`$ needs an induction on that chain through Lemma IX. Now proved for every $`n`$ (§7.1).
- **Not counted** (blocking point about the claimed progress). Each family above is one matrix; only NEST(k) of [COVER.md](COVER.md)
  §6.1 and the schemas range over many matrices. So the claim that the families cover the 12 classes of matrices between $`V_3`$ and
  SRO cannot hold, and "the pattern side is not the obstacle" is a conjecture from a sample of 44 steps (all certified: 32 by a
  generic recipe, 12 by hand certificates). The classes hold 3,166 matrices with at most 7 columns (the paper said 3,167; it
  counted SRO itself). The class is the set of matrices reached from SRO by fundamental sequences with at most 9 intermediate
  columns; that it contains every standard matrix with at most 7 columns is not shown.
- **Open**: UNIF-FS below SRO. What is left: the block shapes of $`\Phi_3(A)`$ and $`\Phi_3(A[n])`$ for every $`A`$, and for each shape a
  derivation in the moves (the conditions of SR* for every block, and the index step of IX by induction). Today this holds for
  about 15 matrices and the families of [COVER.md](COVER.md) §6.1. (Now for 459 of the 3,166 sample matrices, for every $`n`$; §7.1.)

## 2. A native map on the index family

What the lower side needs is a map $`\nu`$ from $`D`$ to RF fan-free patterns with $`\nu(s) \ll \nu(t)`$ at every step ([COVER.md](COVER.md) §6.1).
This paper builds $`\nu`$ without matrices on the index family $`\psi_{\Omega_1}(\Omega_\alpha)`$, $`\omega \le \alpha \lt \varepsilon_0`$.

- **Not counted**: Lemma LOCAL (proved, 1 review): order preservation follows from the local steps $`\alpha \to \alpha+1`$ and
  $`\alpha[n] \to \alpha`$. The referee: this is OE_F of [COVER.md](COVER.md) §5.3 with transitivity of $`\ll`$, so it restates the target.
- **Tools** (proved, 1 review). The point relation $`\ll'`$ of §1 (here with steps that reflect at an element inside a copy and keep
  the rest, example FRAME). Lemma UNIV: if $`x \lt_2 y`$ in a copy, every pattern with no $`\le_2`$-atom has copies cofinally below $`x`$,
  and also below a root $`r \le_1 R`$ with $`r \lt x \lt R`$.
- **The codes $`N(\alpha)`$** (proved, 1 review; Lemma PAT). Defined by recursion on the Cantor normal form of $`\alpha`$: one block per
  term, the blocks nested; the upper part of a block codes the exponent by additively principal points above its right end; at
  limit indices these points carry decorations $`u \le_1 u + E(\mathrm{logend})`$ with small codes $`E`$ in a prefix; a successor index
  raises the innermost top. Each code is a pattern, RF and fan-free. Checked: $`N(\alpha)`$ equals the output of $`\Phi_3`$ on all 50
  pure-index landmarks; 39,700 codes pass the pattern check.
- **Not proved** (blocking point): Theorem IDX, $`N(\alpha') \ll N(\alpha)`$ for $`\omega \le \alpha' \lt \alpha \lt \varepsilon_0`$. The lowering chain
  and the steps $`\alpha \to \alpha+1`$, $`\lambda+n \to \lambda+\omega`$ and the first case of $`\alpha[n] \to \alpha`$ are proved. One step of Lemma
  CODE fails: the written rule can choose a host above the index it should stay below. Counterexample: $`\alpha = \omega^{\omega^{\omega^z}}`$
  with $`z = \omega^{\omega^{\omega+1}} + \omega^{\omega^\omega}`$, $`n = 1`$; there R1 does not apply. The written rule fails on 336 of 4,420 steps of
  this form and on 1,830 of 79,990 random steps; the paper's side check used another rule and skipped the decorations. With that
  other rule: 0 failures on about 99,000 steps (checked, not proved). So the order of $`\Phi_3`$ on the 50 landmarks, which goes
  through IDX, is not proved either. The theorem itself looks true. Even if proved, the fragment has order type $`\varepsilon_0`$, so it
  adds no ordinal to the known part of the core. Now proved with a new host rule (§7.2).
- **Where the index family stops** (proved, 1 review). At $`\varepsilon_0`$ the recursion has no code ($`\mathrm{logend}(\varepsilon_0) = \varepsilon_0`$). The
  least set that contains $`\omega`$ and is closed under $`+`$, $`z \mapsto \omega^z`$ and $`a \mapsto \psi_{\Omega_1}(\Omega_a)`$ lies below
  $`\psi_{\Omega_1}(\Omega_{\Omega_1}) \lt \theta_0`$, misses $`[\varepsilon_0, \upsilon_1)`$ and does not contain $`\upsilon_2`$. So codes that use only the index family prove at
  most $`\psi_{\Omega_1}(\Omega_{\Omega_1}) \le m_F`$, and $`FF_{RF}`$ needs $`\nu`$ on all of $`D`$.
- **Open**: (O1) Lemma CODE for the small codes of $`[\varepsilon_0, \upsilon_1)`$ (a repair up to $`\zeta_0`$ is only outlined; now proved up to $`\varphi_\omega(0)`$, §7.2); (O2) references to
  codes of arbitrary $`\psi_{\Omega_1}`$-terms, which indices $`\ge \upsilon_1`$ need; $`FF_{RF}`$.
- **Tool fix** (checked). The Python port of InaccPsi now flattens sums ([COVER.md](COVER.md) §6.4); with it the base $`I_0\cdot 2`$ gives normal forms.

## 3. Restart reaches between the segments of level 2

Notation of [COVER.md](COVER.md) §6.3: $`u_n = \upsilon^2_n`$, $`x = x_2`$, $`\nu = \nu_C`$, $`S_n = [u_n, u_{n+1})`$, $`S_\omega = [x, \nu)`$. $`V_g`$ and the level $`\gamma(\lambda)`$
are as in [REACHES.md](REACHES.md) §1, and $`\mathrm{Fix}_g`$ is the range of $`V_g`$. A restart index $`\lambda`$ is **Γ-type** if it is in $`\mathrm{Fix}_g`$ for
every $`g \lt \lambda`$ ($`\Lambda_\Gamma`$ is the least one). $`\Psi^{(n)}_g`$ ($`\Psi^{(\omega)}_g`$) is the least member of $`\mathrm{Fix}_g`$ above $`u_n`$ (above $`x`$),
$`P_n = [u_n, \Psi^{(n)}_{\omega^\omega})`$ and $`Q_\omega = [x, \Psi^{(\omega)}_{\omega^\omega})`$. RM says that the reaches of restarts correspond between $`S_n`$ and $`S_\omega`$.

- **Lemma SUP** (proved, 1 review). The formal-reach recursion of TAIL-GAP ([COVER.md](COVER.md) §5.1) is a limit superior of the moved
  values of the earlier restarts. (The referee: the case where cofinally many earlier values are undefined should be stated.)
- **Theorem GEN-OFF.** Theorem OFF-V of [REACHES.md](REACHES.md) §1 holds at every restart index below $`\nu`$ that is not Γ-type, without the
  bound $`\Lambda_\Gamma`$: the offset is $`-1 + e`$ if $`\gamma(\lambda) = 0`$ and $`\lambda = \lambda_0 + \omega^e`$, and $`\rho_\lambda\cdot\gamma + \mathrm{logend}(\alpha)`$ if
  $`\lambda = V_\gamma(\alpha)`$, $`\gamma = \gamma(\lambda) \ge 1`$. The case $`\gamma = 0`$ is proved (1 review); the case $`\gamma \ge 1`$ is an outline (now proved, Theorem LAYERS, §7.3). The referee:
  this gives the reach of every restart below $`\nu`$ that is not Γ-type, also beyond $`P_n`$.
- **Theorem FIX-Γ.** Every point of $`U_2 \setminus \{\nu\}`$ is a fixed point of $`\iota \mapsto \upsilon_\iota`$: $`u_n = \upsilon_{u_n}`$ and $`x = \upsilon_x`$
  (proved, 1 review). Its index is Γ-type (outline; now: $`u_n`$ and $`x`$ are critical and limits of critical indices, FIX-L, §7.3).
- **Outline only** (each through GEN-OFF for $`\gamma \ge 1`$ or the substitution maps of [BREAK.md](BREAK.md) §4): a base change $`T_n`$ from $`P_n`$
  into $`Q_\omega`$, the identity below $`u_n`$ with $`T_n(u_n) = x`$, equal to the FRAG map on every finite set; IMG,
  $`\Psi^{(\omega)}_g \lt \nu`$ for $`g \lt \omega^\omega`$ (from Carlson 2009, Def 5.3 clause 2 at $`x \le_2 \nu`$); RM-P, $`\mathrm{lh}(T_n\rho) = T_n(\mathrm{lh}\,\rho)`$ for every
  restart $`\rho`$ of $`P_n`$; the finite form of LBC that [COVER.md](COVER.md) §6.3 says is enough; SC-P, the condition SC for every
  $`Y \subset Q_\omega`$ and every $`W \subset P_n`$. So the restriction to the first block of $`x`$ in §6.3 of [COVER.md](COVER.md) is gone on the side of
  $`Y`$, and the inner pair of the nested configuration whose top is $`\nu_C`$ is covered. RM-P is also the statement that blocked Theorem
  RED of [BREAK.md](BREAK.md) §8.3 (the same reduction), now settled on $`P_n`$ at outline level. All of these are now proved on the larger part $`D_n \supset P_n`$ (§7.3).
- **Not proved** (blocking point, stated by the paper): RM, LBC and SC in full, and so $`\nu_C = \nu_S`$. SEG-RED needs every
  $`W \subset S_n`$. Beyond $`P_n`$ three things are missing: IMG for $`g \ge \omega^\omega`$, the map $`T_n`$ past the Veblen clauses, and the
  reaches at Γ-type indices (the long restarts). $`Y \subset S_\omega \setminus Q_\omega`$ is open too. No restart where RM fails was found.

## 4. Chains of pairs in the fan-free core

$`\mathrm{CH}_K`$ is the pattern of $`K`$ pairs in a row, $`u_1 \lt_2 v_1 \lt u_2 \lt_2 v_2 \lt \cdots \lt u_K \lt_2 v_K`$, with every $`u_i \le_1 v_K`$ and point $`u_1`$. (The papers also use a form with one more point between 0 and $`u_1`$; the referee: both
forms have the same limit $`m_F`$, and this should be stated.)

- **Theorem WORD** (proved, 1 review). A balanced word $`W`$ of brackets gives an RF fan-free pattern $`P(W)`$: a matched pair of
  brackets gives a $`\lt_2`$-pair, and every position that is not a closing bracket is $`\le_1`$ to the positions before the right end of
  the innermost pair around it. Every RF fan-free
  pattern $`P`$ has a word $`W`$ such that every copy $`Y`$ of $`P(W)`$ contains a copy of $`P`$ inside $`[\min(Y \setminus \{0\}), \max Y)`$. So
  $`\max P^* \lt \max P(W)^*`$.
- **Theorem CH** (proved, 1 review; only R1 and R2, no fan). If $`W`$ has depth at most $`d`$ and width at most $`m`$, and $`K \ge d(m-1)+2`$, then
  every copy of $`\mathrm{CH}_K`$ contains a copy of $`P(W)`$ in $`[u_1, v_K)`$.
- **Corollary CORE-CH** (proved, 1 review). $`\mathrm{Core}_F = \bigcup_k [0, \iota(\mathrm{CH}_k))`$, with
  $`\iota(\mathrm{CH}_k) \lt \max \mathrm{CH}_k^* \lt \iota(\mathrm{CH}_{k+1})`$, so $`m_F = \sup_k \iota(\mathrm{CH}_k)`$: the limit of one explicit sequence of finite patterns.
- **FS-F** (proved for the patterns written out, 1 review). With patterns $`\mathrm{NCH}_k`$ (a chain of $`k`$ pairs with a point below it and some extra points),
  $`\iota(\mathrm{NCH}_k) \lt \iota(\mathrm{CH}_k) \lt \iota(\mathrm{NCH}_{k+1})`$, so $`m_F = \sup_k \iota(\mathrm{NCH}_k)`$. $`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)[n]) prints $`\mathrm{NCH}_{n+1}`$
  for $`n \le 29`$ (checked), so the same holds for these matrices given the printed shapes, not for all $`n`$. (The referee: the step
  $`\iota(\mathrm{NCH}_k) \lt \iota(\mathrm{CH}_k)`$ comes from Carlson 2009, Thm 14.10(2), not from $`\ll`$.)
- **$`\sigma_N = m_F`$** (proved, 1 review). So $`FF_N \Leftrightarrow FF_{RF} \Leftrightarrow H_m`$; $`FF_N`$ of [BREAK.md](BREAK.md) §7.4 is now the same hypothesis.
- **SRO and the chains** (proved, 1 review; it uses R5). $`\Phi_3(\mathrm{SRO}) \ll \mathrm{CH}_2`$ by hand, with SRO as $`\Phi_3`$ prints it (before: one certificate). So POINT-SRO implies
  L1p-HYP by a proof ($`\mathrm{CH}_2`$ is L1p), and $`\iota(\mathrm{CH}_1) \lt \iota(\Phi_3(\mathrm{SRO})) \lt \iota(\mathrm{CH}_2)`$. $`H_m`$ holds iff $`\sup_k \iota(\mathrm{CH}_k) \ge \theta_0`$.
- **The upper bound as one sequence** (proved, 1 review). $`m_F \le t \Leftrightarrow \iota(\mathrm{CH}_k) \lt t`$ for every $`k`$. For $`k = 1`$:
  $`\iota(\mathrm{CH}_1) \le \upsilon_\omega`$. Already $`\iota(\mathrm{CH}_2) \gt \nu_C \gt \Lambda_\varepsilon`$, above every point with a proved upper bound by an InaccPsi term.
- **Relativized chains** (proved, 1 review). For $`v \in V_F`$, chains attached to $`v`$ give an increasing sequence $`\chi_k(v) \lt v^+`$ whose
  limit $`\kappa(v)`$ is the top of the RF fan-free core over $`v`$; so $`\kappa(v) \le v^+`$. Theorem ITER ([COVER.md](COVER.md) §6.2) with the start
  fixed at $`I_0`$ (proved as an implication): if $`\iota(\mathrm{CH}_k) \lt \psi_{\Omega_1}(I_0)`$ for every $`k`$ and (HQ) holds along $`V_F`$, then
  $`x_F \lt \psi_{\Omega_1}(I_0\cdot 2)`$. (The referee: the template $`\psi_{\Omega_1}(I_0)`$ is outside the hypothesis as stated, but the bound still holds
  by `bounded_inter_Om1` with $`X = I_0\cdot 2`$.)
- **Not proved** (blocking point): $`v^+ \gt \kappa(v)`$, and the cost bound that uses it. Only $`\kappa(v) \le v^+`$ is proved; equality is
  REL-SHARP, which is open.
- **Open**: an InaccPsi upper bound for $`m_F`$ (conjecture $`m_F = \psi_{\Omega_1}(I_0)`$), a step that pays for one more pair of the chain
  (STEP-CH; the referee: its bound must be on the collapse arguments, below $`I_0`$, not on the values), REL-SHARP, and (HQ).

## 5. Status after the eighth round

- The lower-bound program below $`\theta_0`$: all 160 neighbour pairs of the sample above $`V_3`$ are proved or certified in the predicted
  order (§1). UNIF-FS below SRO and the map on all of $`D`$ are open; a native map is built on the index family below $`\varepsilon_0`$, but
  its order (IDX) has a gap (§2).
- The first inaccessible: $`H_m \Leftrightarrow FF_{RF} \Leftrightarrow FF_N \Leftrightarrow \sup_k \iota(\mathrm{CH}_k) \ge \theta_0`$ (§4). $`H_m`$ stays open.
- Upper bounds: $`m_F`$ is the limit of the points of the chains $`\mathrm{CH}_k`$, so a bound for $`m_F`$ is a bound for that one sequence;
  no bound by an InaccPsi term is proved for $`m_F`$, $`x_F`$ or $`C^*_3`$.
- $`\nu_C = \nu_S`$: SC holds at outline level for every $`W`$ in the initial part $`P_n`$ of a segment; beyond $`P_n`$ it is open (§3).

## 6. Checks

Each run was under 60 seconds; none is a proof.

- Limit jumps (§1). The 21 hand certificates (20 jumps and LJ2) replay: 21 of 21, also in the referee's rerun. The replay checks only that the point of the copy lies below ($`\ll'`$); $`\ll`$ rests on the
  hand proofs, which is enough for $`\iota`$. Controls: the same step
  lists with the two patterns swapped fail 21 of 21; tampered certificates are rejected; reverse searches for 14 jumps (25 s each)
  found nothing. The 48 hand certificates of the families ($`n = 0`$ to $`3`$) replay; at $`n = 4, 5`$, 21 of 24 replay (failures: LONG-K at
  $`n = 5`$, where $`\Phi_3`$ stops, and IDX-ADD). The copy of $`\Phi_3`$ used is byte-identical to the one in this repository.
- Index codes (§2). The codes equal the output of $`\Phi_3`$ on 50 of 50 landmarks; 39,700 codes pass the pattern check; 7 sample steps
  have replayed certificates, and none was found in the reverse direction.
- Restarts (§3). In the program model, the patterns of the matrices that continue the base of $`S_\omega`$ and those of $`S_n`$
  ($`n = 1`$ to $`5`$) agree on 7,383 comparisons, with long-restart analogues included; the referee's rerun gave 606 equal and 0 different,
  and a control shows that wrong translates match only 2 of 597 times. These are the program's own reaches, not $`R_2^C`$, and the
  columns where the two bases differ were not tested.
- Chains (§4). All 196 balanced words of length at most 12 give patterns; 3,000 random RF fan-free patterns pass every step of the
  proof of WORD. Certificates in the predicted direction: 15, and the referee's 5 more, replayed. In the refuting direction: none in
  6 searches of 50 s and 8 searches of 40 s.

## 7. The ninth round

Four papers, each refereed once (so every result here has 1 review). No paper of this round makes a Lean claim.

### 7.1 The shapes of $`\Phi_3`$ and the step below SRO

$`Z_1`$ = (0,0,0)(1,1,1), and $`\mathrm{sh}_2(B)`$ adds 2 to row 0 of $`B`$. For a matrix $`M`$, $`V(M)`$ is the node set of $`\Phi_3(M)`$ and $`M^\wedge`$ its
point. The text definition of $`\Phi_3`$ is the one in the converter's README and [ALGORITHM-2.md](../../BMS/PoR/Trio/por/ALGORITHM-2.md).
The bad root and $`t`$ are those of the BMS expansion of $`A`$.

- **Lemma G** (proved). By its text definition, $`\Phi_3(M)`$ is one fixed structure $`G`$ on all sums, restricted to $`V(M)`$. Only $`V(M)`$
  depends on $`M`$. That the program equals the text definition is checked (the referee: 15,830 builds, 0 differences), not proved.
- **Lemmas SUMS and IND-SUB** (proved). A copy of $`\Phi_3(A)`$ extends to all sums of its indecomposables, keeping the order and the
  reaches. So if every one-term node of $`\Phi_3(A[n])`$ is a node of $`\Phi_3(A)`$, then $`\Phi_3(A[n]) \ll' \Phi_3(A)`$, with no shape information.
- **Lemma IX-ι** (proved; the referee adds one hypothesis that the paper uses but does not state: the point of the block must not
  involve the index $`c`$). Suppose $`\Phi_3(A)`$ is an index part (the closure of a pair sequence $`c`$) plus a block that refers to $`c`$ only
  through trailing prefixes of $`c`$, and $`\Phi_3(A[n])`$ is the same with $`c[n]`$. Then $`\Phi_3(A[n]) \ll' \Phi_3(A)`$. The proof uses only
  $`\iota(\Phi_3(c[n])) \lt \iota(\Phi_3(c))`$ (Theorem S), Lemma UNIV of §2 and Carlson 2009, Thm 14.10(2): the copy of the new index part is the least
  realization of $`\Phi_3(c[n])`$. So, unlike Lemma IX of §1, it never needs the shape of the index part.
- **Theorem ZB** (proved given LOW; LOW is proved for pair sequences and for nests over them, through the Lean facts `ctps_lh`,
  `stdOrd_lh`, `ctps_anchor`). LOW says that the nodes of $`B`$ lie lexicographically below $`(Z_1\cdot\mathrm{sh}_2(B))^\wedge`$. For a standard trio
  matrix $`B`$ with LOW, $`\Phi_3(Z_1\cdot\mathrm{sh}_2(B))`$ is $`G`$ restricted to the closures of the root terms of $`B`$ plus a block of 4 nodes that refers
  to $`B^\wedge`$. The proof traces every branch of the program; the referee retraced it.
- **IDX-ADD for every $`n`$** (proved; this repairs the blocking point of §1). For A = (0,0,0)(1,1,1)(2,0,0)(3,1,0)(4,1,0)(5,0,0)(6,1,0) and
  B = (0,0,0)(1,1,0)(2,1,0)(3,0,0)(4,1,0), the index part of $`\Phi_3(A[n])`$ is $`\Phi_3(B[n])`$ for every $`n`$, so its explicit shape (a chain of
  1-row towers, checked for $`n \le 12`$) is not needed. A second proof by induction with LOW moves uses that chain.
- **Corollary ZB-FS** (proved). The step holds for every $`n`$ at every $`A = Z_1\cdot\mathrm{sh}_2(B)`$ with $`B`$ a standard pair sequence whose last
  column is not a root column, and at nests of these. (The referee: when $`B`$ has two root terms, the copy of the core is the restricted copy with
  the sums of its prefixes; the rest is unchanged.)
- **Corollary IND** (proved). If the bad root is a root column and $`t = 0`$ ("successor at a root"), every one-term node of $`\Phi_3(A[n])`$ is one
  of $`\Phi_3(A)`$, so the step holds by IND-SUB. This covers 372 sample matrices and every such matrix beyond the sample.
- **Theorem SELF-top** (proved, after a one-word fix by the referee: the summands must lie in the first block $`I_0`$). In the
  self-reference type (the bad root is column 0, $`t \ge 1`$) BMS gives $`A[n] = A'\cdot\mathrm{sh}(A[n-1])`$. If $`\Phi_3(A[n])`$ is $`\Phi_3(A[n-1])`$ plus a
  block of the shape of the top block, the previous root occurs only as a last summand and in the top, and the base block fits below
  the top, then the step holds for every $`n`$. That a given matrix satisfies these hypotheses is checked only ($`n \le 3`$).
- **The proved class on the sample** (the 3,166 limit matrices between $`V_3`$ and SRO with at most 7 columns of §1): 459 proved for every
  $`n`$ (IND 372, ZB with a pair core 78, nested ZB 9), for the text definition of $`\Phi_3`$; 21 more given LOW, which is checked for $`n \le 2`$ only.
- **Not proved** (blocking points, against the conditional classes only).
  - "167 matrices with a pair core are proved given checked shapes": IX-ι needs the top node of the block to have $`c`$ as a summand. In 9
    of the 167 (and in 6 trio cores) $`c`$ occurs only inside a term, for example (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,0,0)(5,0,0). So at most 158.
  - "The hypotheses of SELF-top hold for 62 matrices ($`n \le 3`$)": the base step fails when a node of $`I_0`$ reaches into the first block.
    This happens for 4 of the 62, for example (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0). So at most 58.
- **Open**: UNIF-FS below SRO for all matrices. The sample split by where the bad root $`R`$ sits:

| where $`R`$ sits | matrices | proved for every $`n`$ | the rest |
|---|---|---|---|
| inside an index term | 581 | 108 | 392 pass the decomposition check for $`n \le 2`$; 81 fail it |
| in a later summand | 603 | 166 | 437 open |
| column 0 | 635 | 206 | 429 open (the self-reference type) |
| in the $`\Omega`$-level structure | 1,347 | 0 | open; no decomposition found |

  The 480 proved include the 21 that are proved given LOW. (Now 874 proved, §10.1, and 1,442, [VEBLEN.md](VEBLEN.md) §3.) What is missing, class by class: that $`\Phi_3`$ treats the index term as one unit
  in every context; a copy of the changed summand that interleaves with the fixed earlier summands (a CODE lemma with parameters, the
  same kind of gap as in §2); the shapes of the self-reference type for every $`n`$; and, for the last class (it contains POINT-REF, LONG-K and
  the type of SRO itself), any decomposition.

### 7.2 Native codes past $`\varepsilon_0`$, and patterns below $`\mathrm{CH}_2`$

Notation of §2 and §4. The configuration L1p is a $`\lt_2`$-pair inside the reach of an earlier left end, beyond that left end's right
end ($`x_1 \lt_2 y_1 \lt x_2 \lt_2 y_2`$ with $`x_1 \le_1 x_2`$, $`x_1 \le_1 y_2`$; [BREAK.md](BREAK.md) §7.4). A pattern is L1p-free if it has no copy of it.

- **Lemma HOST** (proved). The new host rule: a new index $`g`$ is placed directly below the least old index above $`g`$ in its layer. That
  index is $`h = c + \omega^\rho`$ with $`g = c + \delta`$, $`\delta \lt \omega^\rho`$. So $`h`$ is a limit, $`\mathrm{logend}(g) \lt \mathrm{logend}(h)`$, and $`h`$ is at or below every old
  index that $`g`$ is compared with.
- **Lemma CODE′** (proved; it replaces Lemma CODE of §2). With this rule every new index has a host, the realized order is the index
  order, and every decoration needed is smaller than the host's in the realized order. So $`N(\gamma + \omega^{b'}) \ll N(\gamma + \omega^b)`$ for every
  $`1 \le b' \lt b`$, not only for $`b' = b[n]`$. In the counterexample of §2 the new index $`\omega`$ now has the host $`\omega^\omega`$. (The referee: when a decoration
  has two or more summands, the set that is placed must also contain its partial sums, which R4 gives; the proof goes through.)
- **Theorem IDX** (proved; this repairs the blocking point of §2). $`N(\alpha') \ll N(\alpha)`$ for $`\omega \le \alpha' \lt \alpha \lt \varepsilon_0`$.
- **Theorem IDX′** (proved). With the measure $`m(\varphi_j(\xi)) = (j, \xi)`$ at $`\varepsilon`$-numbers and the decorations $`p \le_1 p\cdot(k+1) + E(\mu)`$,
  the codes $`N(\alpha)`$ are defined for $`\omega \le \alpha \lt \varphi_\omega(0)`$, they are RF fan-free patterns, and $`N(\alpha') \ll N(\alpha)`$ for $`\alpha' \lt \alpha`$
  there. Past $`\varphi_\omega(0)`$ the decorations need more points inside the reach: outline only. Now ordered up to the Bachmann–Howard ordinal with other codes (§10.2).
- **Lemma REF** (proved). If $`Q' \ll Q`$ and $`T`$ refers to $`Q`$ only through its point, then $`T`$ with $`Q'`$ in place of $`Q`$ is $`\ll T`$. But references do
  not raise the order type: a family closed under sums and references to index codes stays below $`\psi_{\Omega_1}(\Omega_{\Omega_1}) \lt \theta_0`$
  (§2). So what is left is the whole map $`\nu`$ on $`D`$, not "(O1), then (O2)".
- **Theorem HOST2** (proved). In every copy of $`\mathrm{CH}_2`$, every L1p-free RF fan-free pattern has copies cofinally below $`u_1`$. So
  $`\max P^* \lt \iota(\mathrm{CH}_2)`$ for every L1p-free RF fan-free pattern $`P`$. No condition on interior sums is needed. (The referee: the enlarged pattern in the proof
  uses a new indecomposable, so it is a pattern only up to isomorphism; that is enough, and it keeps RF, fan-free and L1p-free.)
- **Corollaries** (proved). Every code $`N(\alpha)`$ with $`\alpha \lt \varphi_\omega(0)`$ and every native family so far (the towers $`A_n`$ for every $`n`$,
  SRO and others) is $`\ll \mathrm{CH}_2`$. So $`\iota(\mathrm{CH}_2) \ge \varphi_\omega(0)`$; this is far below the known $`\iota(\mathrm{CH}_2) \gt \nu_C`$.
- **Reduction RED-ν2** (proved). A map $`\nu`$ from $`D`$ to L1p-free RF fan-free patterns with $`\nu(s) \ll \nu(t)`$ at every step gives
  $`\iota(\mathrm{CH}_2) \ge \theta_0`$, hence $`m_F \gt \theta_0`$ and $`H_m`$: the first fan needs $`I_0`$.
- **Not proved**: the target "the codes of a family cofinal below $`\theta_0`$ are $`\ll \mathrm{CH}_k`$, so the first fan needs $`I_0`$". $`A_n \ll \mathrm{CH}_2`$ is
  proved, but the lower bound $`\iota(A_n) \ge |\tau_n|`$ for every $`n`$ is not ($`|\tau_n|`$ is the value of the $`n`$-th tower term, $`\tau_{n+1} = \Omega_{\tau_n}`$,
  and these values are cofinal in $`\theta_0`$); it is the same lower-bound problem. Equivalently, the map $`\nu`$ of RED-ν2 on all of $`D`$ is missing; it is proved only on $`[\omega, \varphi_\omega(0))`$. The paper says
  so itself.
- **Not counted**: the paper's claim that the calculus proves $`\iota(P) \ge \delta`$ only through a natively increasing family of order type $`\delta`$.
  It is a claim about every possible derivation; the referee calls it a remark, not a theorem.

### 7.3 Restart reaches up to the first limit of critical indices

Notation of §3. The **layers** over $`\upsilon`$: $`C^1 = \mathrm{Fix}_1`$, the fixed points of $`\iota \mapsto \upsilon_\iota`$. In layer $`\xi`$, $`W^{(\xi)}_0`$ enumerates $`C^\xi`$,
$`\mathrm{Fix}^{(\xi)}_{j+1}`$ is the set of fixed points of $`W^{(\xi)}_j`$ in $`\mathrm{Fix}^{(\xi)}_j`$ (intersections at limits), and $`W^{(\xi)}_j`$ enumerates $`\mathrm{Fix}^{(\xi)}_j`$; for $`\xi = 1`$
these are the $`V_{1+j}`$. $`C^{\xi+1}`$ is the set of $`\iota \in C^\xi`$ that lie in $`\mathrm{Fix}^{(\xi)}_j`$ for every $`j \lt \iota`$ (intersections at limits). $`C^2`$ is the set of
Γ-type indices. An index $`\iota`$ is **critical** if $`\iota \in C^\iota`$. $`\chi^{(n)}_\omega`$ ($`\chi^{(\omega)}_\omega`$) is the least limit of critical indices above $`u_n`$
(above $`x`$), and $`D_n = [0, \chi^{(n)}_\omega)`$. $`\rho^2 = \rho\cdot\rho`$ and $`\rho^3 = \rho\cdot\rho\cdot\rho`$. The paper numbers these levels one lower.

- **Lemma LB** (proved). $`\mathrm{Fix}^{(\xi)}_j \subseteq [j, \infty)`$ and $`C^\xi \subseteq [\xi, \infty)`$. So every $`\iota \in \mathrm{Fix}_1`$ that is not critical has a unique canonical
  form $`(\xi, j, \eta)`$, all three below $`\iota`$, with $`\iota = W^{(\xi)}_j(\eta)`$.
- **Theorem LAYERS** (proved; in $`R_2^S`$ and $`R_2^C`$). For every restart index $`\lambda`$ with $`\rho_\lambda \lt \nu`$ that is not critical,
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + O(\lambda)`$ with $`O(\lambda) = -1 + \mathrm{logend}(\lambda)`$ at level 0 and, for the canonical form $`(\xi, j, \eta)`$,
  $`O(\lambda) = b_\xi(\rho) + \rho\cdot j + \mathrm{logend}(\eta)`$, where $`\rho = \rho_\lambda`$, $`b_1(\rho) = \rho`$ and $`b_\xi(\rho) = \rho^2\cdot(-1+\xi)`$ for $`\xi \ge 2`$. Layer 1 is the
  offset $`\rho\cdot\gamma + \mathrm{logend}(\alpha)`$ of GEN-OFF (§3) with no bound and no outline step, so GEN-OFF for $`\gamma \ge 1`$ is now proved.
- **Corollary CR1** (proved). A critical index that is not a limit of critical indices has offset $`\rho^3`$; the least limit of critical
  indices above a base has offset $`\rho^3 + 1`$ (the reach $`\delta + \rho^3 + 1`$ there follows from TAIL-GAP with that base; the referee: this step should be
  written). So the reach of every restart below $`\nu`$ is known, except at limits of critical indices.
  Every long restart and every point of level 2 has such an index.
- **Corollary FIX-L** (proved). $`u_n`$ and $`x`$ are critical and are limits of critical indices. This replaces the outline half of FIX-Γ (§3).
  The critical indices $`\chi^{(n)}_k`$ ($`k \le \omega`$) above $`u_n`$ lie in $`S_n`$.
- **Lemma TRANS** (proved; $`R_2^C`$, from Carlson 2009, Def 5.3 clause 2 at $`x \le_2 \nu`$). A finite family of restarts whose reaches are at least
  $`\delta + t(\rho)`$ ($`t`$ an offset term with constants from a fixed finite set) that occurs cofinally below $`x`$ also occurs cofinally below $`\nu`$
  above $`x`$. The witness: the $`R_1^+`$ relations $`p \le_1 p + q`$ inside block 0 of a restart force the exponents of the copied offset; $`+`$ alone
  cannot. (The referee: the proof applies an earlier lemma outside its stated hypotheses; this is correct, but the variant should be stated as a lemma.)
- **Theorem IMG-D** (proved). $`\chi^{(\omega)}_\omega \lt \nu`$. So $`\Psi^{(\omega)}_g \lt \nu`$ for every $`g`$ below the least Γ-type index above $`x`$ (IMG of §3 was an
  outline for $`g \lt \omega^\omega`$).
- **Lemma T** (proved, after a one-line repair by the referee of one comparison rule). A map $`T_n : D_n \to [0, \chi^{(\omega)}_\omega)`$, the identity below
  $`u_n`$, with $`T_n(u_n) = x`$, commuting with $`\upsilon`$, with every $`W^{(\xi)}_j`$ and with the critical points. It is strictly increasing and
  additive, and keeps $`\varepsilon`$-numbers, additive principal numbers, $`\upsilon`$-points, layers, levels and criticality in both directions. Every
  finite subset of $`[0, \chi^{(\omega)}_\omega)`$ lies in its image for all large $`n`$.
- **RM-D, LBC$`^{fin}`$-D and SC-D** (proved). $`\mathrm{lh}(T_n\rho) = T_n(\mathrm{lh}\,\rho)`$ for every restart $`\rho`$ of $`D_n \cap S_n`$; the finite form of LBC on $`D_n`$; and
  SC for every finite $`Y \subset [x, \chi^{(\omega)}_\omega)`$ and every $`W \subset D_n`$. These prove the outlines of §3 ($`T_n`$, IMG, RM-P, the finite LBC,
  SC-P) on the larger part $`D_n \supset P_n`$.
- **Conjecture KV.** Beyond $`\chi^{(n)}_\omega`$ the offsets are $`\sum_\xi \rho^\xi\cdot a_\xi + \mathrm{logend}(a_0)`$ (the pattern of Klammersymbols), up to $`\rho^\rho`$.
  The six program points beyond $`D_n`$ fit it. Now proved (Theorem KV, §10.3).
- **Not proved** (blocking point, stated by the paper): RM, LBC and SC beyond $`D_n`$, and so $`\nu_C = \nu_S`$. SEG-RED needs $`W`$ anywhere in $`S_n`$,
  and every point of $`(u_n, \chi^{(n)}_\omega)`$ has reach at most $`\delta + \rho^3 + 1 \lt \delta\cdot 2`$, so the push-down step of SEG-RED cannot be
  placed inside $`D_n`$. Missing: canonical forms and offsets above $`\chi^{(n)}_\omega`$ (KV), a collapsing notation over $`\upsilon`$ at a critical base,
  and the restarts at limits of critical indices whose formal reach is undefined. $`Y \subset S_\omega \setminus [x, \chi^{(\omega)}_\omega)`$ is open too. No restart
  where RM fails was found.

### 7.4 Toward an InaccPsi upper bound for $`\iota(\mathrm{CH}_2)`$

Notation of §4, in $`R_2^C`$. $`\mathrm{lh}(a) = \sup\{g : a \le_1 g\}`$, $`L_2`$ is the set of $`\lt_2`$-left ends, $`\sigma_2(a)`$ is the least $`b`$ with $`a \lt_2 b`$, $`p_2(\beta)`$
is the least $`d`$ such that some $`c`$ in $`(\beta, d)`$ has $`c \lt_2 d`$, $`T_j(\beta)`$ is the least top $`v_j`$ of a copy of $`\mathrm{CH}_j`$ above $`\beta`$, and
$`N(a) = \sup\{j : T_j(\sigma_2(a)) \le \mathrm{lh}(a)\}`$, the number of further chains inside the reach of $`a`$.

- **Lemma ATOMS** (proved). For $`a \lt b \lt c \lt d`$: $`\{0, a, b, c, d\}`$ is a covering of $`\mathrm{CH}_2^*`$ iff $`a \le_2 b`$, $`c \le_2 d`$ and $`a \le_1 d`$. Then
  $`\mathrm{CH}_2^*`$ is pointwise below $`(a, b, c, d)`$ and $`\iota(\mathrm{CH}_2) \le a`$. No two of the three relations imply the third.
- **Lemma GREEDY** (proved). $`\mathrm{CH}_2^* = (a^*, b^*, c^*, d^*)`$ with $`b^* = \sigma_2(a^*)`$, $`d^* = p_2(b^*)`$, $`c^* = \min\{c : b^* \lt c \lt_2 d^*\}`$, and
  $`a^* = \iota(\mathrm{CH}_2) = \min\{a \in L_2 : p_2(\sigma_2(a)) \le \mathrm{lh}(a)\}`$.
- **Theorem REACH-FORM** (proved). $`\iota(\mathrm{CH}_k) = \min\{a \in L_2 : N(a) \ge k-1\}`$, and $`N(\iota(\mathrm{CH}_k)) = k-1`$. So $`m_F \le t`$ iff for every $`k`$ some
  $`a \lt t`$ in $`L_2`$ has $`N(a) \ge k`$. Fan apexes have $`N = \infty`$. (The referee: when $`\mathrm{lh}(a)`$ and $`T_j`$ are both $`\infty`$, "$`T_j \le \mathrm{lh}(a)`$" must be read
  as false; harmless.)
- **Corollary** (proved). $`\iota(\mathrm{CH}_2) \lt t`$ iff one point $`a \lt t`$ has $`a \lt_2 b`$, a pair $`c \lt_2 d`$ with $`b \lt c`$, and $`a \le_1 d`$. No two of the three
  are enough.
- **FLOOR** (proved). Every such $`a`$ is $`\ge \iota(\mathrm{CH}_2) \gt \nu_C \gt \Lambda_\varepsilon`$. A candidate $`a \ge \omega_1^{CK}`$ gives nothing, because
  $`\iota(\mathrm{CH}_2) \lt \omega_1^{CK}`$ (Carlson 2009, Thm 15.2 with Thm 14.14).
- **STAB** (its $`\le_1`$ part proved). If $`L_a \prec_{\Sigma_1} L_\beta`$ with $`\beta`$ admissible and $`a \lt g \lt \beta`$, then $`a \le_1 g`$; and every such $`a \gt \omega + 1`$ is
  $`\ge \omega_1^{CK}`$. So reflection in $`L`$ gives only useless candidates. Not proved: the paper's addition that clause 1 of $`\le_2`$ holds too (its proof
  uses $`a`$ as a parameter inside $`L_a`$, where $`a`$ is not an element). The claim that every set-theoretic source gives only such candidates is a
  remark, not a theorem.
- **Not counted**: GEN-REST. It is proved but trivial (an increasing map into $`t`$ exists iff $`\iota(\mathrm{CH}_2) + 1 \le t`$); the referee: its content
  stays open.
- **Not proved** (blocking point): "STEP-CH is equivalent to the reach form". STEP-CH is universal (for every $`A`$ in a class and every $`k`$); the
  reach form gives only $`\iota(\mathrm{CH}_{k+1}) \le \psi_{\Omega_1}(\Phi^k(a_1))`$ for each $`k`$. What holds: STEP-CH on a class closed under $`\Phi`$ implies the
  reach form, which gives $`m_F \le \sup_k \psi_{\Omega_1}(\Phi^k(a_1))`$.
- **Open**: an InaccPsi upper bound for $`\iota(\mathrm{CH}_2)`$, so for every $`\iota(\mathrm{CH}_k)`$ and for $`m_F`$. The three relations at a point above $`\nu_C`$ are positive
  relations of $`R_2^C`$, and under Carlson 2009, Def 5.3 they get harder to meet when the interval has more relations (NO-HALF). The paper
  says a proof needs to know which configurations do not occur on $`[a, d]`$; the referee: not in general, since positive relations also follow
  from positive relations (Carlson 2009, L.5.5, L.5.7(3), Thm 14.10), as the case of fan apexes shows. What is missing is names for the points,
  the exact structure of $`R_2^C`$ above $`\Lambda_\varepsilon`$, or an order embedding of Carlson's closure there.

## 8. Status after the ninth round

- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 459 of the 3,166 sample matrices (21 more given LOW),
  on every successor at a root and on every nest $`Z_1\cdot\mathrm{sh}_2(B)`$ over a pair sequence; IDX-ADD is proved for every $`n`$. The rest is in four
  open classes (§7.1). The native codes are ordered up to $`\varphi_\omega(0)`$ (§7.2).
- The first inaccessible: $`H_m`$ is open. It now follows from $`\iota(\mathrm{CH}_2) \ge \theta_0`$, which follows from a map $`\nu`$ on all of $`D`$ with L1p-free
  values and $`\ll`$ at every step (HOST2, RED-ν2; §7.2).
- Upper bounds: $`\iota(\mathrm{CH}_2) \lt t`$ is exactly three relations at one point $`a \lt t`$, and that point is above $`\nu_C`$ (§7.4). No InaccPsi bound is
  proved for any $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$ or $`C^*_3`$.
- $`\nu_C = \nu_S`$: the reach of every restart below $`\nu`$ is known except at limits of critical indices; SC is proved on $`D_n \supset P_n`$; beyond $`D_n`$ it is
  open (§7.3).

## 9. Checks of the ninth round

Each run was under 60 seconds; none is a proof.

- Shapes (§7.1). Theorem ZB holds exactly on all 218 sample matrices of its form and their expansions for $`n \le 4`$ (1,128 of 1,128); the
  referee checked 797, 1,553, 472 and 46 more cases. The program equals the text definition on 15,830 builds. IND: 304 new matrices with
  8–11 columns, 1,216 steps. The index cores and their expansions $`c[0..2]`$ are standard for all 248 pair-core matrices (yaBMS). Generic
  certificates for the self-reference type replay for 125 of 146 matrices at every $`n = 0`$ to $`3`$.
- Codes (§7.2). The host rule in realized order: 572,150 steps, 0 failures; two altered rules are caught; the referee's run with a new seed:
  about 283,000 steps, 0 failures. Every pattern that $`\Phi_3`$ prints for the 10,633 standard matrices below SRO with at most 7 columns and for
  1,423 landmarks is L1p-free (given the printed shapes); in the scanned tree of fundamental sequences the first pattern with L1p is
  $`\mathrm{NCH}_2`$ (scanned: those matrices and the tree of depth at most 3 below (0,0,0)(1,1,1)(2,2,1), with the printed shapes, which can be wrong). Certificates in the predicted direction: 15, and the referee's 2, replayed. In the refuting direction ($`\mathrm{CH}_2 \lt P`$ for
  L1p-free $`P`$): none found, in 2 searches by the paper and 4 searches of 50 s by the referee.
- Restarts (§7.3). In the program model at base 0, 21 standard matrices: the 15 layer points read exactly the offsets of LAYERS and CR1
  ($`\rho^2`$, $`\rho^2+1`$, $`\rho^2+\rho`$, $`\rho^2\cdot 2`$, $`\rho^2\cdot\omega`$, $`\rho^2\cdot\omega^2`$, $`\rho^3`$), and the 6 beyond fit KV. The referee reproduced this byte for byte,
  checked 7 new strings ($`\rho^3 + 1`$ at the first limit of critical indices, $`\rho^3`$ at the next critical ones, $`\rho^2`$ at the next Γ-type points),
  and compared the segments at 6 new seeds: 12 equal, 0 different. These are the program's own reaches, not $`R_2^C`$.
- Chains (§7.4). Of 924 trio matrices between $`\mathrm{NCH}_2`$ and $`\mathrm{NCH}_3`$, none prints exactly $`\mathrm{CH}_2`$; only exact equality was tested, so a
  pattern that is $`\mathrm{CH}_2^*`$ plus extra nodes would be missed. The referee: over 1,890 matrices below $`\mathrm{NCH}_3`$ and 686 below $`\mathrm{NCH}_4`$, no
  pattern has a copy of $`\mathrm{CH}_k`$ at or below its point, so no counterexample to $`\iota(\mathrm{NCH}_k) \lt \iota(\mathrm{CH}_k)`$ or to any proved item.

## 10. The tenth round

Four papers, each refereed once, so every result here has 1 review. One paper (§10.4) checked a Lean test file of named points with
leanman (green, and green again in the referee's rerun); that file only compares terms, and it is not added to the library. The other
three papers make no Lean claim.

### 10.1 The shapes of $`\Phi_3`$: the classes I, SUM, ROOT and III

Notation of §7.1. The four classes of the table in §7.1 are named by where the bad root $`R`$ sits: I (inside an index term), SUM (in a later
summand), ROOT (column 0) and III (in the $`\Omega`$-level structure). FS$`^+(A)`$ means $`\Phi_3(A[n]) \ll' \Phi_3(A)`$ for every $`n`$. The theorems are about
the text definition of $`\Phi_3`$; that the program agrees with it is checked only. Everything is in $`R_2^C`$.

- **Lemma IX-ι, restated** (proved). The hypothesis found missing in §7.1 is now part of the statement: the top node of the block has a
  prefix of $`c`$ as its last summand. A summand 1 may sit anywhere (Lemma N0 below).
- **Lemma CHAIN** (proved, after a repair by the referee). If the top node has no such summand, but the slack reaches the point through a
  chain of nested blocks, the copy is built by R1 applied block by block. The referee: the paper says "innermost block first", but the
  proof lowers outer blocks first, and then a later stage can meet a letter that is already moved. Repair: skip a block whose root is already
  moved; the skipped stages are never needed. CHAIN proves 6 of the 9 matrices of the blocking point of §7.1 (the other 3 have a successor
  step at the index root) and 14 more.
- **SELF-top with (B0′)** (proved). Every relation of $`\Phi_3(A[0])`$ whose left element lies in the first block must also hold in the copy. This
  repairs the second blocking point of §7.1. Whether a matrix satisfies the hypotheses is still checked only for $`n \le 3`$ (58 matrices).
- **STD-ROOT and N0** (proved). Every root term of a standard matrix is standard. Every copy can be normalized so that its least plain
  indecomposables are $`1, \omega, \omega^2, \ldots`$; in particular $`1 \mapsto 1`$. (The referee: the definition of "standard" that STD-ROOT cites is not in
  [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md); the proof works for any seed family of single root terms.)
- **Theorem SUM-LOW and Corollary SUM-PAIR** (proved). Let $`A = Q + c`$ with $`c`$ the last root term, a pair term or $`Z_1`$. If three conditions on $`Q`$
  alone hold ((Q1) the only indecomposable of $`V(Q)`$ below $`Z_1`$ is 1; (Q2) Lemma UNIV of §2 holds at the least other indecomposable of $`V(Q)`$;
  (Q3), only for $`c = Z_1`$, a condition on $`Z_1`$), then FS$`^+(A)`$. A trio term $`c`$ reduces to a placement of the smaller matrix $`c`$ (proved as a
  reduction; the placement is open). (The referee: the lemma CL-LOC used here is true only with its trailing clause.)
- **Lemma SYM** (proved as a paper argument about the program's Python semantics; not machine-checked). Run the program on $`F[b]`$, where $`b`$ is
  an index that refuses every read whose answer could depend on it. If the run finishes, it gives $`\Phi_3(F[c])`$ for every pair root term $`c`$
  (not the leaf, first child with $`y \le 1`$) at once. Two rewrites of the program are needed; both are exact identities. The paper left one point
  checked only (76 identity tests); the referee's run with a faithful second rewrite gives the same templates, so this point is settled for
  the contexts below.
- **Theorems I-SYM and III-SYM** (proved). For 31 contexts $`F`$ of class I, and 12 of class III where the pair subterm hangs under a column with
  $`z = 0`$: FS$`^+(F[c])`$ for every $`n`$ and every standard pair root term $`c`$ of the class. So in these contexts $`\Phi_3`$ treats the index term as one
  unit.
- **Not counted**: the paper's "reduction" for ROOT with $`t = 1`$. No symbolic run finishes (302 of 302 stop at the same point), so the
  referee calls it vacuous.
- **The proved classes on the sample** of §1 (3,166 matrices). Each count below counts members of classes defined by finite conditions,
  and these classes are infinite.

| class | matrices | proved for every $`n`$ | given LOW | given a condition checked for small $`n`$ | open |
|---|---|---|---|---|---|
| I | 581 | 210 | 21 | 0 | 350 |
| SUM | 603 | 418 | 0 | 7 | 178 |
| ROOT | 635 | 206 | 0 | 58 | 371 |
| III | 1,347 | 40 | 0 | 0 | 1,307 |
| all | 3,166 | 874 (before: 459) | 21 | 65 | 2,206 |

- **Not proved** (blocking point, bookkeeping only): the paper's list of the "exact open parts" is not complete. 267 of the 2,206 open sample
  matrices fall under none of its items: 77 of class I whose step is a successor at the index root, and 104 + 86 of class III where $`R`$ is a
  (0,0) column with $`t = 2`$, or with $`t = 1`$ and a trio subterm. So the list below is not exhaustive.
- **Open**: UNIF-FS below SRO. The listed parts: the placement for small trio cores such as $`Z_1`$(1,1,1), $`Z_1`$(1,1,0), $`Z_1`$(2,0,0); 10 contexts of
  class I and 52 of class III where the program reads the index itself; ROOT with $`t \ge 1`$ for every $`n`$ (it needs a symbol for the periodic
  term $`A[m]^\wedge`$; every step with $`t = 1`$, in any class, substitutes the matrix into itself in this way); III with $`t = 0`$, and III where $`R`$ is a
  column with $`z = 1`$ or $`y \ge 1`$; and the 267 matrices above.

### 10.2 Native codes up to the Bachmann–Howard ordinal

Notation of §2 and §7.2. $`B`$ is the Bachmann–Howard ordinal, $`\vartheta^2_0`$ of Wilken, "Ordinal arithmetic based on Skolem hulling" (APAL 145,
2007), Def 3.13 and Thm 3.14; $`\vartheta`$ is Wilken's $`\vartheta_0`$ there, and $`a^*`$ is the largest countable additive principal subterm of $`a`$.

- **The ordinals below $`B`$** (cited; the referee checked the places and their hypotheses). Every additive principal $`g \lt B`$ is $`\vartheta(a)`$ for one
  $`a \lt \varepsilon_{\Omega_1+1}`$ with $`a^* \lt g`$; $`g`$ is an $`\varepsilon`$-number iff $`a = \Omega_1\cdot\delta + \eta`$ with $`\delta \ge 1`$, $`\eta \lt \Omega_1`$; two values are compared by
  Lemma 3.30 of that paper.
- **Lemma TAU** (proved). $`\tau_g`$, which replaces $`\Omega_1`$ by $`g`$, is an order isomorphism onto its image, and the shift $`\sigma_{g\to h}`$ is strictly increasing.
- **The codes and Lemma PAT-B** (proved). For an $`\varepsilon`$-number index $`g = \vartheta(\Omega_1\cdot\delta + \eta)`$ the prefix point $`p(g)`$ gets the reach $`E(\zeta(g))`$ with
  $`\zeta(g) = g\cdot\tau_g(\delta)\cdot 2 + \eta`$. The indices between $`g`$ and the top of $`\zeta(g)`$ are its satellites; they are ordinary indices, not $`\varepsilon`$-numbers.
  Every code is an RF fan-free, L1p-free pattern, and the reach intervals of the prefix are nested or disjoint (the factor 2 is what gives
  this). Below $`\varepsilon_0`$ the codes are those of §2 (checked on 1,041 indices); above $`\varepsilon_0`$ they differ from those of §7.2, and both families are valid.
- **Lemmas HOST-B and ZC** (proved). If $`h`$ is the least old index above a new $`\varepsilon`$-number index $`g`$, then $`h`$ is an $`\varepsilon`$-number, $`a_g \lt a_h`$, and
  $`\sigma_{g\to h}(\zeta(g)) \lt \zeta(h)`$.
- **Lemma CODE-B** (proved). A new $`\varepsilon`$-number index is placed together with its satellites: they are realized inside the reach of $`p(h)`$ by the shift
  $`g \to h`$, and then the whole group is reflected below $`p(h)`$ by R1. Copies only need coverings, so no negative relation has to be produced.
- **Theorem IDX-B** (proved). $`N(\alpha') \ll N(\alpha)`$ for $`\omega \le \alpha' \lt \alpha \lt B`$. With HOST2 (§7.2): $`\iota(\mathrm{CH}_2) \ge B`$ (before: $`\varphi_\omega(0)`$). This is still far below
  the known $`\iota(\mathrm{CH}_2) \gt \nu_C`$.
- **Remark** (not counted): past $`B`$ the rule breaks; the reach of a satellite crosses the reach of its index, and the reach must be the fold of
  [PSS/POR.md](../../BMS/PoR/PSS/POR.md) §3.3. The paper says the first failure is at $`\vartheta_0(\vartheta_1(\Omega_2\cdot 2))`$; the referee: the smaller index
  $`\vartheta_0(\vartheta_1(\Omega_2 + 1))`$ already fails, and at $`B`$ itself the two reach tops are equal (the open case EQUAL-TOP).
- **Not proved**: the map $`\nu`$ of RED-ν2 on all of $`D`$. The gap has three parts: codes and $`\ll`$ steps on $`[B, \upsilon_1)`$ (folded reaches, with the case
  EQUAL-TOP); then the references for indices $`\ge \upsilon_1`$; then the block grammar of the $`\Omega`$-levels. The paper says so itself. (The referee: the
  names of the Veblen and Klammer landmarks that the paper gives are neither cited nor proved; nothing uses them.)

### 10.3 Klammer sets over $`\upsilon`$ and the reaches up to $`\rho^\rho`$

Notation of §3 and §7.3. A symbol $`A`$ is a finite map from positions $`\xi \ge 1`$ to coefficients $`a_\xi \ge 1`$, ordered by the top position where two
symbols differ. The paper defines, with no literature, clubs $`F_A`$ with enumerations $`\varphi_A`$, starting from $`\varphi_0 = \upsilon`$: $`F_A`$ is the set of $`\eta`$
that are fixed by every $`\varphi_B`$ with $`B`$ below $`A`$ in the Klammer sense and entries below $`\eta`$. So $`F_{(1@1)} = \mathrm{Fix}_1`$, $`\varphi_{(g@1)} = V_g`$, $`F_{(1@2)}`$ is the
set of Γ-type indices and $`F_{(1@3)}`$ the set of critical indices. $`K`$ is the set of indices fixed by every $`\varphi_B`$ with entries below them, and $`k`$
enumerates $`K`$. $`P_A(\rho) = \sum_\xi \rho^\xi\cdot a_\xi`$. A restart is **long** if its reach is at least $`\delta\cdot 2`$. The paper numbers the levels one lower.

- **The Klammer hierarchy** (proved). The $`F_A`$ are clubs; FIX and LB-coef; below its top position $`F_A`$ meets only $`K`$ (ANOM). Every index in
  $`\mathrm{Fix}_1 \setminus K`$ has one canonical form $`(A, \eta)`$, all entries below it. A comparison rule (it contains the repair of Lemma T in §7.3) and a
  membership rule (the referee: its third case is valid only after the first). The layers, levels and critical indices of §7.3 are the symbols with
  positions $`\le 2`$ and $`F_{(1@3)}`$.
- **Theorem KV** (proved; it was Conjecture KV of §7.3). For every restart index $`\lambda \notin K`$ with $`\rho_\lambda \lt \nu`$ and canonical form $`(A, \eta)`$:
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + P_A(\rho) + \mathrm{logend}(\eta)`$, $`\rho = \rho_\lambda`$, and this offset is below $`\rho^\rho`$. LAYERS and CR1 are special cases. (The referee: in one
  subcase of the lower bound the chosen point may not exist; the repair takes it by continuity of $`\varphi_A`$. "Conjecture KV" here means this
  hierarchy, not a Klammer theory from the literature.)
- **CR-K, CR-K2, FIX-K** (proved). At $`k(\beta)`$ with $`\beta \lt k(\beta)`$ the offset is $`\rho^\rho + \mathrm{logend}(\beta)`$; at a fixed point of $`k`$ that is not a limit of
  fixed points of $`k`$ it is $`\rho^\rho + \rho`$. Every point of $`U_2 \setminus \{\nu\}`$ is in $`K`$, is a fixed point of $`k`$ and is a limit of fixed points of $`k`$;
  every long restart has such an index.
- **IMG-K** (proved). The $`\omega`$-th point of $`K`$ above $`x`$ is below $`\nu`$.
- **Lemma T#, RM#, LBC$`^{fin}`$#, SC#** (proved). Let $`u^\#`$ be the next point of $`F_{(1@u)}`$ above $`u`$; $`[u, u^\#)`$ holds the points whose canonical
  positions are all below $`u`$ (the paper writes one direction; the referee: the converse is true but not written). On $`D^\#_n = [0, u_n^\#) \supset D_n`$ the map $`T_n`$ of §7.3 keeps reaches, the finite LBC holds, and SC holds for every finite
  $`Y \subset [x, x^\#)`$ and every $`W \subset D^\#_n`$.
- **PROP LONG and NEED-C** (proved; the second in a weaker wording, as the referee notes). In SEG-RED the push-down always lands on a long
  restart of $`S_n`$, above $`D^\#_n`$. Every long restart lies in **zone C**: in every tail below it some restart has no formal reach. So SEG-RED needs SC for
  sets $`W`$ that meet zone C, and no closed form of the reaches can give that.
- **Not proved** (blocking point, stated by the paper): $`\nu_C = \nu_S`$, and RM and SC for $`W`$ that meet zone C. **Open**: between $`u_n^\#`$ and the
  $`\omega`$-th point of $`K`$ above $`u_n`$, $`T_n`$ needs $`u_n`$ and $`x`$ to have the same membership profile for symbols with positions $`\ge u_n`$ (PROF); and
  the reaches at limits of fixed points of $`k`$.

### 10.4 Names past $`\Lambda_\varepsilon`$, and the claim up to $`\rho_{\Lambda'+\omega^2}`$

Notation of [PINS.md](PINS.md) §2–§3: $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`D`$, $`\iota(\eta)`$, $`\eta_\lambda`$, $`e_\lambda = \mathrm{logend}(\eta_\lambda)`$, and the formal
offset $`c^+`$. $`\zeta_{\Omega_1+1}`$ is the least fixed point of $`\alpha \mapsto \varepsilon_\alpha`$ above $`\Omega_1`$, and $`\zeta^r`$ the same above $`r`$.
$`\Lambda' = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\zeta_{\Omega_1+1}+1}})`$.

- **EPS-THETA** (proved, from Wilken 2007 (APAL 145, 130–161), L.3.30, 4.3, 4.4). For a $`\upsilon`$-point $`\tau`$, $`\eta \mapsto \vartheta^\tau(\Omega_1 + \eta)`$ lists in order the
  $`\varepsilon`$-numbers above $`\tau`$, below the next $`\upsilon`$-point, that are not fixed points of $`\alpha \mapsto \varepsilon_\alpha`$; the first fixed point is
  $`\zeta^\tau = \vartheta^\tau(\Omega_1\cdot 2)`$.
- **EXACT-Z** (proved). Wilken's base change moves exactly every offset term built from small constants, the base $`x`$, $`\zeta^x`$, $`+`$, $`\omega^{\cdot}`$ and $`\varepsilon_{\cdot}`$
  below $`\varepsilon_{\zeta^x+1}`$ (before: only Cantor normal forms in $`x`$).
- **Theorem NAME-OFFSET-Z** (proved). For every restart index $`\lambda`$ in the range of GEN with $`e_\lambda \le \varepsilon_{\zeta_{\Omega_1+1}+1}`$:
  $`c^+(\lambda) = (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$ (with $`\zeta_{\Omega_1+1}`$ sent to $`\zeta^{\rho_\lambda}`$). This contains NAME-OFFSET of [PINS.md](PINS.md) §3, and proves
  Conjecture NAME-OFFSET+ there for these offsets.
- **THETA-P** (proved; a conjecture before). $`\Theta_P = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+\omega}})`$. Also: the least restart with $`c^+ = \zeta_{\rho+1} + 1`$ is
  $`\Lambda_\zeta = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\zeta_{\Omega_1+1}+1})`$, $`c^+(\Lambda') = \varepsilon_{\zeta^\rho+1}`$, and $`\Lambda' \lt \Theta_1`$.
- **Not proved** (false as stated): "for every term $`t`$ the least $`\lambda`$ with $`c^+(\lambda) \ge t`$ is $`\iota(\omega^{1+t})`$". It needs $`\omega^{1+t} \in D`$; the referee's
  counterexample is $`t = \Xi_1 = H(\Omega_1)`$. THETA-P has finite constants and is not affected.
- **STRUCT′** (proved). On $`[0, \rho_{\Lambda'+\omega^2})`$, in $`R_2^C`$ and $`R_2^S`$ (they agree there): the $`\lt_2`$-pairs are exactly $`(H(\eta_\lambda + \omega\cdot j), H(\eta_\lambda + \omega\cdot j + 1))`$; a
  restart $`\rho_\lambda = H(\eta_\lambda)`$ has $`\rho_\lambda \le_1 g`$ iff $`g \le H(\eta_\lambda + \omega + 1) + (-1 + e_\lambda)[\Omega_1 := H(\eta_\lambda)]`$; every other point has its $`R_1^+`$
  reach inside its block. (The referee: the paper's "every atom named" is too strong; inside a block $`\le_1`$ is given by $`R_1^+`$, not by an InaccPsi
  expression.)
- **Wilken's claim on $`[0, \rho_{\Lambda'+\omega^2})`$ in $`R_2^C`$**, both halves (proved): every ordinal below
  $`\rho_{\Lambda'+\omega^2} = H(\varepsilon_{\zeta_{\Omega_1+1}+1} + \omega^2) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\zeta_{\Omega_1+1}+1}} + \omega^{\theta+2})`$ is in the core and is the value of an InaccPsi
  normal form with collapse arguments below $`I_\omega`$. Before: $`[0, \Lambda_\varepsilon)`$. The referee: for the claim itself the only new fact is the position
  $`\Lambda' + \omega^2 \le \Theta_1`$, because the core part was known up to $`\nu_C`$; and the upper bound $`\mathrm{Core} \subseteq \psi_{\Omega_1}(I_\omega)`$ does not move. The paper
  states $`\rho_{\Theta_1} \gt \rho_{\Lambda'+\omega^2}`$ but proves only $`\ge`$; NAME-OFFSET-Z at $`\Lambda' + \omega^2`$ gives the strict form in one line. **Remark** (the
  referee's, not counted): the same proof reaches $`H(\varepsilon_{\zeta_{\Omega_1+1}+1}\cdot\omega + \omega^2)`$.
- **NAME-LAYERS** (proved). For a restart index $`\lambda \le \Lambda'`$ with $`e = e_\lambda`$: $`\lambda \in C^\xi`$ ($`2 \le \xi \lt \lambda`$) iff $`e \ge \Omega_1^2\cdot(-1+\xi)`$, and $`\lambda`$ is
  critical iff $`e \ge \Omega_1^3`$. So the first limit of critical indices at base 0 is $`\chi^0_\omega = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1^3+1}) \lt \Lambda_\varepsilon`$. (The referee: $`e`$ fixes
  the canonical form only up to the last exponent of its third entry; the step uses the earlier result that the two formal reaches agree.)
  TRANS, Lemma T and FIX-L were not needed: they matter only in the segments of level 2, above $`\nu_P`$.
- **$`\iota(\mathrm{CH}_2)`$** (proved). $`\iota(\mathrm{CH}_2) \gt \iota(\Phi_3(\mathrm{SRO})) \gt \nu_C \gt \nu_P \gt \rho_{\Theta_1} \ge \rho_{\Lambda'+\omega^2}`$. Below $`\nu_C`$ no point has the three relations of §7.4,
  so this structure gives no bound for $`\iota(\mathrm{CH}_2)`$. Conjecture: $`\iota(\mathrm{CH}_2) \gt \theta_0`$.
- **Open**: offsets up to $`\Gamma_{\rho+1}`$ (one more lemma, VEB-THETA, and a uniform comparison of Veblen forms); $`\Theta_1 = H(\theta)`$ (the maps STEP and
  LOW-STEP one level down); the names of $`\Theta_1`$, $`\Theta_A`$, $`\Theta_\delta`$, $`\Theta_{d\omega}`$, $`\Lambda^*`$, $`\nu_P`$; an InaccPsi upper bound for $`\nu_C`$ (it would give the claim on
  $`[0, \nu_C]`$). (Now the offsets up to $`\psi_{\Omega_2}(\Omega_2) + 1`$, past $`\Gamma_{\rho+1}`$, are proved, and $`\Theta_1 = H(\theta)`$ is reduced to one hull lemma, [VEBLEN.md](VEBLEN.md) §1.)

## 11. Status after the tenth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, \rho_{\Lambda'+\omega^2})`$ (§10.4); $`\Theta_P`$ has its name.
- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 874 of the 3,166 sample matrices (§10.1); the native codes
  are ordered up to the Bachmann–Howard ordinal, so $`\iota(\mathrm{CH}_2) \ge B`$ (§10.2). UNIF-FS and the map $`\nu`$ on all of $`D`$ are open.
- The first inaccessible: $`H_m`$ is open; it would follow from $`\iota(\mathrm{CH}_2) \ge \theta_0`$.
- Upper bounds: no InaccPsi bound is proved for any $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$ or $`C^*_3`$; $`\iota(\mathrm{CH}_2)`$ lies above $`\nu_C`$.
- $`\nu_C = \nu_S`$: the reach of every restart below $`\nu`$ is known except at limits of fixed points of $`k`$ (§10.3); SC is proved on $`D^\#_n \supset D_n`$; what is left
  is SC for sets that meet zone C, which SEG-RED always needs.

## 12. Checks of the tenth round

Each run was under 60 seconds; none is a proof.

- Shapes (§10.1). The symbolic templates equal the concrete $`\Phi_3`$ on every sample member of every proved context for $`n \le 3`$, in text and
  program mode. The referee, on the unpatched program: 10,760 builds of $`F[c]`$ with random pair indices $`c`$ (standard and not, up to 10
  columns) and 4,680 expansions, 0 differences; 1,349 members of the class of SUM-PAIR beyond the sample, 0 failures.
- Codes (§10.2). The group placement in realized order: 99,371 steps, with 188,989 new $`\varepsilon`$-number indices and 100,733 satellites, 0 failures;
  18,539 random codes are RF fan-free, L1p-free patterns; three altered rules are caught. 8 certificates in the predicted direction (among
  them $`N(\vartheta(\Omega_1^2))`$, $`N(\vartheta(\Omega_1^\omega))`$ and $`N(\vartheta(\Omega_1^{\Omega_1}))`$ below $`\mathrm{CH}_2`$) replay; 2 reverse searches found nothing. The referee: the
  order axioms of the ordinal comparison on 6.1 million triples, ZC on about 175,000 pairs, HOST-B on 52,000 hard cases, nesting of reach intervals on
  10,700 codes, and a placement run with a new seed (31,917 steps): 0 failures.
- Restarts (§10.3). In the program model at base 0 the first point of $`K`$ reads $`\rho^\rho`$, then $`\rho^\rho + 1`$ and $`\rho^\rho + \rho`$, as CR-K and CR-K2 say. The
  referee reproduced this byte for byte; of 12 new probes, the 9 that KV covers read its values ($`\rho^2`$, $`\rho^2 + 1`$, $`\rho^2 + \rho`$, $`\rho^3`$, $`\rho^3 + \rho`$, $`\rho^\omega`$, $`\rho`$,
  $`\rho^{\omega^2}`$, $`\rho^{\omega+1}`$). These are the program's own reaches, not $`R_2^C`$.
- Names (§10.4). The 25 named points are normal forms and strictly increasing, in Python and in a Lean test file (green, also in the referee's
  rerun). On 300 random offsets $`e`$ below $`\zeta_{\Omega_1+1}`$, $`\omega^e \in D`$ and $`e \mapsto H(\omega^e)`$ keeps the order (89,700 pairs, 0 failures). The referee: 250 random
  offset terms at 5 bases, 124,500 comparisons, 0 mismatches. (The referee also notes that the test of $`D`$ used only the constants $`H(0)`$ and $`H(1)`$,
  where the hypothesis missing from ATTAIN-NAMES does not matter.)

## 13. Open

The eleventh round changed this list; the current list is on the next page, [VEBLEN.md](VEBLEN.md) §7.
