[← Back](README.md) | [English](FANFREE.md) | [Japanese](FANFREE-ja.md)

# $`R_2^+`$, the eighth round: the limit jumps, a native map on the index family, restart reaches between segments, and chains in the fan-free core

This page continues [COVER.md](COVER.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from 2026-10. They
come from the eighth round of four papers, each refereed once, so a result has 1 review unless a count is given. "2 reviews"
means that two independent papers proved the result and each paper was refereed once. A result marked **outline** was found
"proved (outline)" by its referee; it is not counted as proved. A statement with a blocking point against it is listed under
**Not proved**, even when the rest of its paper is proved. A true statement that its referee found to restate the target, or to
claim more progress than it gives, is listed under **Not counted**. A certificate counts only when it was replayed. As in
[COVER.md](COVER.md) §5–§6, the papers number the levels of nested pairs one lower than these pages; here they are renumbered.
None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009,
p. 97, announces. No result on this page is in Lean, and no Lean file was added. The referees rechecked the Lean files that the
papers use: `TrioCofinal.lean` (`trio_fs`, `trio_cofinal`, behind S-RED of [README.md](README.md) §3), `CountSeg.lean` and `LowSeg.lean`.

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
  with 2–3 more LOW moves. A proof for all $`n`$ needs an induction on that chain through Lemma IX.
- **Not counted** (blocking point about the claimed progress). Each family above is one matrix; only NEST(k) of [COVER.md](COVER.md)
  §6.1 and the schemas range over many matrices. So the claim that the families cover the 12 classes of matrices between $`V_3`$ and
  SRO cannot hold, and "the pattern side is not the obstacle" is a conjecture from a sample of 44 steps (all certified: 32 by a
  generic recipe, 12 by hand certificates). The classes hold 3,166 matrices with at most 7 columns (the paper said 3,167; it
  counted SRO itself).
- **Open**: UNIF-FS below SRO. What is left: the block shapes of $`\Phi_3(A)`$ and $`\Phi_3(A[n])`$ for every $`A`$, and for each shape a
  derivation in the moves (the conditions of SR* for every block, and the index step of IX by induction). Today this holds for
  about 15 matrices and the families of [COVER.md](COVER.md) §6.1.

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
  adds no ordinal to the known part of the core.
- **Where the index family stops** (proved, 1 review). At $`\varepsilon_0`$ the recursion has no code ($`\mathrm{logend}(\varepsilon_0) = \varepsilon_0`$). The
  least set that contains $`\omega`$ and is closed under $`+`$, $`z \mapsto \omega^z`$ and $`a \mapsto \psi_{\Omega_1}(\Omega_a)`$ lies below
  $`\psi_{\Omega_1}(\Omega_{\Omega_1}) \lt \theta_0`$, misses $`[\varepsilon_0, \upsilon_1)`$ and does not contain $`\upsilon_2`$. So codes that use only the index family prove at
  most $`\psi_{\Omega_1}(\Omega_{\Omega_1}) \le m_F`$, and $`FF_{RF}`$ needs $`\nu`$ on all of $`D`$.
- **Open**: (O1) Lemma CODE for the small codes of $`[\varepsilon_0, \upsilon_1)`$ (a repair up to $`\zeta_0`$ is only outlined); (O2) references to
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
  $`\lambda = V_\gamma(\alpha)`$, $`\gamma = \gamma(\lambda) \ge 1`$. The case $`\gamma = 0`$ is proved (1 review); the case $`\gamma \ge 1`$ is an outline. The referee:
  this gives the reach of every restart below $`\nu`$ that is not Γ-type, also beyond $`P_n`$.
- **Theorem FIX-Γ.** Every point of $`U_2 \setminus \{\nu\}`$ is a fixed point of $`\iota \mapsto \upsilon_\iota`$: $`u_n = \upsilon_{u_n}`$ and $`x = \upsilon_x`$
  (proved, 1 review). Its index is Γ-type (outline).
- **Outline only** (each through GEN-OFF for $`\gamma \ge 1`$ or the substitution maps of [BREAK.md](BREAK.md) §4): a base change $`T_n`$ from $`P_n`$
  into $`Q_\omega`$, the identity below $`u_n`$ with $`T_n(u_n) = x`$, equal to the FRAG map on every finite set; IMG,
  $`\Psi^{(\omega)}_g \lt \nu`$ for $`g \lt \omega^\omega`$ (from Carlson 2009, Def 5.3 clause 2 at $`x \le_2 \nu`$); RM-P, $`\mathrm{lh}(T_n\rho) = T_n(\mathrm{lh}\,\rho)`$ for every
  restart $`\rho`$ of $`P_n`$; the finite form of LBC that [COVER.md](COVER.md) §6.3 says is enough; SC-P, the condition SC for every
  $`Y \subset Q_\omega`$ and every $`W \subset P_n`$. So the restriction to the first block of $`x`$ in §6.3 of [COVER.md](COVER.md) is gone on the side of
  $`Y`$, and the inner pair of the nested configuration whose top is $`\nu_C`$ is covered. RM-P is also the statement that blocked Theorem
  RED of [BREAK.md](BREAK.md) §8.3 (the same reduction), now settled on $`P_n`$ at outline level.
- **Not proved** (blocking point, stated by the paper): RM, LBC and SC in full, and so $`\nu_C = \nu_S`$. SEG-RED needs every
  $`W \subset S_n`$. Beyond $`P_n`$ three things are missing: IMG for $`g \ge \omega^\omega`$, the map $`T_n`$ past the Veblen clauses, and the
  reaches at Γ-type indices (the long restarts). $`Y \subset S_\omega \setminus Q_\omega`$ is open too. No restart where RM fails was found.

## 4. Chains of pairs in the fan-free core

$`\mathrm{CH}_K`$ is the pattern of $`K`$ pairs in a row, $`u_1 \lt_2 v_1 \lt u_2 \lt_2 v_2 \lt \cdots \lt u_K \lt_2 v_K`$, with every $`u_i \le_1 v_K`$ and point $`u_1`$.

- **Theorem WORD** (proved, 1 review). A balanced word $`W`$ of brackets gives an RF fan-free pattern $`P(W)`$: a matched pair of
  brackets gives a $`\lt_2`$-pair, and every position that is not a closing bracket is $`\le_1`$ to the positions before the right end of
  the innermost pair around it. Every RF fan-free
  pattern $`P`$ has a word $`W`$ such that every copy of $`P(W)`$ contains a copy of $`P`$ below its largest element. So
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
  $`x_F \lt \psi_{\Omega_1}(I_0\cdot 2)`$.
- **Not proved** (blocking point): $`v^+ \gt \kappa(v)`$, and the cost bound that uses it. Only $`\kappa(v) \le v^+`$ is proved; equality is
  REL-SHARP, which is open.
- **Open**: an InaccPsi upper bound for $`m_F`$ (conjecture $`m_F = \psi_{\Omega_1}(I_0)`$), a step that pays for one more pair of the chain
  (STEP-CH), REL-SHARP, and (HQ).

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

- Limit jumps (§1). The 21 hand certificates (20 jumps and LJ2) replay: 21 of 21, also in the referee's rerun. Controls: the same step
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

## 7. Open

- The first inaccessible: $`H_m`$ (equivalently, some $`\iota(\mathrm{CH}_k) \ge \theta_0`$; the map on all of $`D`$ with $`\nu(s) \ll \nu(t)`$ at every step;
  UNIF-FS below SRO with the shapes of $`\Phi_3`$ for every matrix); Lemma CODE and the order of the index codes (IDX); codes beyond
  $`\varepsilon_0`$ (O1, O2).
- Upper bounds: any InaccPsi bound for $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$; STEP-CH; REL-SHARP; (HQ).
- $`\nu_C = \nu_S`$: SC for $`W`$ that meet $`S_n \setminus P_n`$ and for $`Y \subset S_\omega \setminus Q_\omega`$ (IMG for $`g \ge \omega^\omega`$, $`T_n`$ past the Veblen
  clauses, the reaches at Γ-type restart indices); the outlines of §3 (GEN-OFF for $`\gamma \ge 1`$, $`T_n`$).
- The rest of [COVER.md](COVER.md) §9.
