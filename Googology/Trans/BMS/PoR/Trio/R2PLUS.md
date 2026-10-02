[← Back](POR.md) | [English](R2PLUS.md) | [Japanese](R2PLUS-ja.md)

# Theory: $`R_2^+`$ below $`\upsilon_{\omega^3}`$

The rules of $`\Phi_3`$ in [POR.md](POR.md) are checked numerically. This page records the first theorems about
$`R_2^+`$ itself that decide order questions for $`\Phi_3`$. They are proved on paper (not yet
published as a full text, not in Lean) and were checked twice by an independent referee.

**Two structures.** Carlson, "Patterns of resemblance of order 2" (APAL 158, 2009) defines
$`\le_1, \le_2`$ by coverings (his Defs 5.3, 5.4) and says the equivalence with the usual
definition by $`\Sigma_n`$-elementarity "will be established elsewhere"; no proof of it was found
in the literature. Write $`R_2^S`$ for the $`\Sigma_n`$ structure and $`R_2^C`$ for Carlson's. The
certificate search used in [POR.md](POR.md) implements $`R_2^C`$. For order 1 there is no such
issue: Carlson 2001, Wilken 2007 and Carlson–Wilken 2012 all use the same $`\Sigma_1`$ definition
of $`R_1^+`$.

**Results in $`R_2^S`$.** Write $`\upsilon_\iota`$ for Wilken's points with $`\upsilon_1 = \psi_0(\Omega_\omega)`$.
- **Lemma L.** In $`R_1^+`$, a $`\lt_1`$-chain starting at $`z_0 \in T^\tau \cap (\tau, \tau^\infty)`$ has at most
  $`\mathrm{ht}_\tau(z_0) + 2`$ elements; every infinite $`\lt_1`$-chain consists of $`\upsilon`$-points and has
  supremum $`\upsilon_\lambda`$ with $`\lambda`$ a limit.
- **Theorem A.** $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ is the least $`\lt_2`$-pair. On $`[0, \upsilon_{\omega+1}]`$ the
  relation $`\le_1`$ is that of $`R_1^+`$, there is no other $`\lt_2`$, and
  $`\mathrm{lh}(\alpha) = \min(\mathrm{lh}_{R_1^+}(\alpha), \upsilon_{\omega+1})`$.
  The proof follows Wilken's "A glimpse of $`\Sigma_3`$-elementarity" (2020), Thm 21.13, with his
  base transformation ([W07b] Cor 5.7) in place of a translation.
- **Theorem B.** Below $`\upsilon_{\omega\cdot\omega}`$ the $`\lt_2`$-pairs are exactly
  $`\upsilon_{\omega k} \lt_2 \upsilon_{\omega k+1}`$, each $`\upsilon_{\omega k+1}`$ is closed, and inside each block
  $`R_2^S`$ agrees with $`R_1^+`$. The proof, with its Lemma C, is complete and refereed.
- **Proposition P′.** For the trio matrices of four shapes below $`\upsilon_{\omega+1}`$ (369 of the
  538 standard matrices of the first test set), the isominimal realization of $`\Phi_{3m}(M)`$
  puts the point at $`\mathcal{T}_3(M)`$ (the translation of `por/tr3.py`). The shape
  hypotheses were checked on those matrices, not proved for all. As a consequence, 20
  undecided pairs of [POR.md](POR.md) §9 are decided "$`\lt`$" in $`R_2^S`$.

**The two structures agree on this range (Theorem EQ).** $`R_2^C`$ and $`R_2^S`$ have the same
$`\le_1`$ and $`\le_2`$ on $`[0, \upsilon_{\omega+1}]`$ and the same cap on reaches. For $`\le_1`$, one direction
copies a $`\Sigma_1`$-isomorphic copy and replaces each value by its leading term (Carlson 2001,
Lemmas 3.2, 3.13); the other uses Claim 5.5(b) in the proof of [W07b] Thm 5.3, which excludes
exactly the coverings of Carlson's Def 5.3. For $`\le_2`$, the only pair is again
$`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$. With Carlson 2009, Thm 14.10, Proposition P′ and the 20 decided
pairs therefore hold in $`R_2^C`$, the structure the certificate search implements. (Carlson's
clause 2 of Def 5.3 is read as "$`X \cup Y`$ closed", as in his own proofs of Lemmas 5.5(6) and
5.7(3).) The referee found no gap in Theorem EQ. [W07b] only sketches Cases 2 and 3 of Claim 5.5(b); a proof
of them (and of Case 1 of Claim 5.6) from [W07b] Thm 2.2 and the fact "$`x + c = c`$ iff $`c \ge x\omega`$" is now
written and refereed: proved, with only minor points (a page number and a missing status marker). A check below
$`\varepsilon_0`$ finds no covering among the 14,447 and 448 candidates of the two cases; with one term removed
from the set it finds coverings for 200 of 202 values, so the check can fail. The referee's own checks (0
failures) also cover Case 1 of Claim 5.6 and values above $`\varepsilon_0`$: with the 2-row structure as the
reference, Case 2 on 158 values above $`\varepsilon_0`$ and the explicit copies on 114,832 pairs; with one term
removed from the set, a covering is found for 144 of 153 values, so this check can fail too. The agreement up to $`\upsilon_{\omega\cdot\omega}`$ is Theorem EQB below.

**Order preservation on a class of trio matrices (Theorem S).** Let
$`U = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1)`$, so that $`\mathcal{T}_3(U) = \upsilon_{\omega+1}`$. Let
$`R_P`$ be the matrices $`\le_{\mathrm{lex}} U`$ that are non-increasing sums of three kinds of root terms:
pair-sequence terms (no $`z = 1`$), the $`\upsilon`$-points $`\upsilon_n, \upsilon_\omega, \upsilon_{\omega+1}`$, and a
$`\upsilon_n`$ or $`\upsilon_\omega`$ followed by standard pair-sequence children. On $`R_P`$ the pattern of
$`\Phi_3`$ has a short explicit form $`\Phi_3^{\mathrm{exp}}`$ (the 2-row $`\Phi`$ below $`\upsilon_1`$, the
$`\upsilon`$-nodes, and each point with its reach), and for $`M, M' \in R_P`$:

```math
M \lt_{\mathrm{lex}} M' \iff \iota(\Phi_3^{\mathrm{exp}}(M)) \lt \iota(\Phi_3^{\mathrm{exp}}(M'))
```

in both $`R_2^S`$ and $`R_2^C`$, with $`\iota = \mathcal{T}_3`$. This is proved on paper from the cited results,
Theorems A and EQ, Lemma L, Proposition P′ and the 2-row results, and was checked by the
referee. To read it as a statement about standard matrices and the current rule `por/phi3def2.py`, two links
are needed, and both are now proved on paper.
- Every matrix of $`R_P`$ is standard: proved on paper, and the referee found no gap. The proof
  reaches each matrix from $`(0,0,0)(1,1,1)(2,2,2)`$ by explicit expansions. It uses the Lean lemmas
  `expandRL_append`, `expandRL_of_m0_zero`, `expandRL_zeroRow` and the pair-sequence results. Two
  short lemmas are on paper only: a middle block does not change the expansion of the tail, and a
  shift commutes with expansion when the last column has $`x \gt 0`$.
- $`\Phi_3^{\mathrm{exp}}`$ equals the pattern of `por/phi3def2.py` on $`R_P`$: proved on paper, by
  following the labelled branches of [por/README.md](por/README.md) for each shape. The referee read
  it against the code and found no error, and no counterexample in 65,000 new cases. The two facts
  it needs about pair sequences are in Lean: the 2-row closure keeps standard sums standard
  (`ctps_lh`, `stdOrd_lh`, `ctps_anchor`), and a root term of a standard sum is standard
  (`stdOrd_iff`).

**Two further shapes.** The rest of the range below $`U`$ also contains single terms of two further
shapes and sums with such a summand. For them the remark of Carlson–Wilken 2012 §7 is now proved
on paper in the form that is needed, without Wilken's JSL 72 paper. The referee found no gap.
- **Theorem S+.** Let $`\sigma`$ be an epsilon number and $`Q \subseteq [\sigma\omega, \sigma^\infty)`$ finite and
  closed under additive decomposition, $`\mathrm{lh}`$ and $`\mathrm{bar}`$. A map $`h`$ that keeps $`\lt`$, $`+`$
  and $`\le_1`$ on $`Q`$, sends principal numbers to principal numbers, has $`h \ge \mathrm{id}`$ on the
  parameters and keeps $`Q`$ above $`\sigma`$ has $`h \ge \mathrm{id}`$ on all of $`Q`$.
- **Theorem M (the §7 remark, needed form).** Let $`C_\sigma(\beta)`$ be the closure of $`\{0, \sigma, \beta\}`$
  under additive decomposition, $`\mathrm{lh}`$ and $`\mathrm{bar}`$. If it is finite, then
  $`C_\sigma(\beta) \cap [\sigma\omega, \infty)`$ is $`\sigma`$-isominimal and contains $`M(\sigma, \beta)`$.
- **Least copy.** For the matrices of the two shapes in the test set, $`\mathcal{T}_3(M)`$ is the least
  copy of $`\Phi_{3m}(M)`$ in $`R_2^S`$. The hypotheses on each matrix (its nodes are closed under
  $`\mathrm{lh}`$ and $`\mathrm{bar}`$) were checked on these matrices, not proved for all.

So the 10 further pairs below $`\upsilon_{\omega+1}`$ are "$`\lt`$" in $`R_2^S`$, and, by Theorem EQ and
Carlson 2009 Thm 14.10, in $`R_2^C`$ (given the checked hypotheses).

**Theorem S on all standard matrices below $`U`$: proved on paper and refereed.** A proof for
every standard trio matrix $`M \le_{\mathrm{lex}} U`$ was written. It takes a term down one segment by
replacing each nested copy of its root by the root's $`m`$-th expansion; on values this is Wilken's
base change. The first referee found a gap in the step that carries patterns through this map
(Theorem Pi-PAT): a sum step may compare with an element of the copied block, and the chosen $`m`$
did not bound the size of the other terms (example: $`(0,0,0)(1,1,1)(1,1,0)(2,2,0)`$ with $`m = 2`$).
The gap is now closed:
- **Lemma BLK.** On the side of the term, a sum step never removes an element of the copied block.
- **Lemma POP.** On the side of the image, the removal stops at the image block once $`m \gt H(t)`$.
- **Lemma INV.** $`H(t)`$ is the largest rise in $`t`$ (the longest chain on which $`y`$ grows by 1). No
  node of the closure has a larger rise, and the shape, the parameters and the level are kept.
- **Lemma Pi-ORD′** replaces Pi-ORD; with Lemma PARAM it compares parameters and lower nodes with
  the image block.
- The allowed $`m`$ are $`m \ge \max(m_0(t), H(t)+1, \mathrm{Lev}(t))`$. This bound depends on $`t`$ only, so
  finiteness (Lemma TERM) follows from Pi-PAT.

A second referee found Parts I and II (the patterns, Pi-PAT and TERM) proved; they do not use
[W07b] Thm 2.2. The rest (the base change, Theorems A and EQ, S+) uses [W07b] Thm 2.2 in both
directions. Its minor points are now fixed in the text:
- Lemma W2: in the transitivity step, $`\alpha`$ is put into $`Y`$ first, so the second copy lands in
  $`[\alpha, \beta)`$.
- The $`\Sigma_1`$-substructure test used in [W07b] Thm 5.3 (Lemma CRIT) is proved in both
  directions. It is also in Wilken, "A glimpse of $`\Sigma_3`$-elementarity" (2020), Prop 21.6.
- The non-epsilon step is rewritten with three new lemmas (SUMM: $`T^\tau[\sigma]`$ keeps the summands
  of its elements and is closed under $`+`$; LOG: the exponent formula for $`\vartheta^b(\eta)`$; PE: for a
  non-epsilon $`y = \omega^\zeta`$, $`\zeta \in T^\tau[\sigma]`$ and $`\pi(y) = \omega^{\pi(\zeta)}`$). The case that
  cannot occur is now excluded.
- Lemma LEAST-C lists every relation of $`R_2`$ that the proof of the least copy reads. Each is
  decided in $`R_2^C`$ by Theorem EQ, so the least copy is taken in $`R_2^C`$ also for copies with values
  above $`\upsilon_{\omega+1}`$.

**[W07b] Thm 2.2: proved on paper and refereed.** The theorem says: for $`0 \lt \xi \le \alpha`$,
$`\alpha \le_1 \alpha + \xi`$ holds if and only if $`\alpha = \omega^{\alpha'}`$ with $`\mathrm{logend}(\alpha') \ge \xi`$
($`\mathrm{logend}(\beta)`$ is the exponent of the last term of the Cantor normal form of $`\beta`$). Its
proof, and that of [W07b] Lemma 2.1, is only in Wilken 2006, which is not available. Both
directions, Lemma 2.1 and the finite-set test for $`\le_1`$ are now proved from the definition of
$`\le_1`$ and Cantor-normal-form arithmetic only. The converse direction is an induction on
$`(\alpha, \xi)`$ in lexicographic order that builds the copy explicitly. The referee checked every case
and found only minor points (one sentence was missing: $`0 \le_1 b`$ holds only for $`b = 0`$; it is now written
in as a lemma, and every step that uses $`x = 0`$ is written out). The text with these fixes was refereed
again: every step of Lemma 2.1, of both directions and of the consequences was checked, with no FATAL or
BLOCKING point; the referee's checks below $`\varepsilon_0`$ (about 11,100 candidates and 221 copies) and against
the 2-row structure (1,885 terms) found 0 failures. So
Theorem S on all standard matrices below $`U`$, and Theorems A, EQ and S+, no longer depend on an
unavailable paper.

Checks (each run under 60 seconds): the theorem holds on all 58,764 standard matrices $`\le U`$ with
at most 8 columns and on 3,000 random ones with 9–30 columns. Pi-PAT with all the invariants holds
on 8,484 segment terms (at most 8 columns) and 2,878 random ones, and a sum step never enters the
block on either side. The referee's own search (798 segment terms from 802 new matrices with 12–60
columns, and 585 terms at $`m + 2`$) found no counterexample; without the bound $`H(t)+1`$, 13 of the
585 terms fail, so that bound is needed. Pi-PAT was checked again at three values of $`m`$
($`m^*`$, $`m^*+1`$, $`m^*+3`$) on the same 12,745 terms, and membership in the class at three values of $`m`$
per level on the 58,764 and 3,000 matrices: 0 failures (for 6 of the 798 terms the counters were
lost to the time limit). A second referee ran 500 new random matrices with 9–45 columns at
$`m^*+2`$ and $`m^*+5`$: 483 of 483 segment terms pass.

Checks of [W07b] Thm 2.2 (each run under 60 seconds, 0 failures): the explicit copies of the
converse direction on 2 × 2,000 random cases below $`\varepsilon_0`$ (a wrong $`\mathrm{logend}`$ gives
non-isomorphic copies in 93 and 116 of 1,000 cases, so the check can fail); with the 2-row
$`\mathrm{lh}`$ as the reference, the theorem on 1,091 principal terms and the copies on 79,376 cases. The referee's own
check: 3,000 random cases, and every one of 649 wrong copies is caught.

**Theorem S below $`\upsilon_{\omega\cdot\omega}`$: proved on paper and refereed.** For $`k \ge 1`$ let $`V_k`$ be
`(0,0,0)(1,1,1)`, then $`k`$ copies of `(1,1,0)(2,2,1)(2,0,0)`, then `(1,1,0)(2,2,1)`. So $`V_1 = U`$ and
$`V_2 = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1)`$. Let
$`V = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)`$. Then $`\mathcal{T}_3(V_k) = \upsilon_{\omega k+1}`$,
$`\mathcal{T}_3(V) = \upsilon_{\omega\cdot\omega}`$, and $`V[N]`$ has the value $`\upsilon_{\omega(N+1)}`$. For all
standard trio matrices $`M, M' \lt_{\mathrm{lex}} V`$, with $`\Phi_3`$ = `por/phi3def2.py`:

```math
M \lt_{\mathrm{lex}} M' \iff \iota(\Phi_3(M)) \lt \iota(\Phi_3(M')), \qquad \iota(\Phi_3(M)) \lt \upsilon_{\omega\cdot\omega},
```

in both $`R_2^S`$ and $`R_2^C`$, and $`\iota(\Phi_3(V_k)) = \upsilon_{\omega k+1}`$. The referee found no FATAL or
BLOCKING point, only three minor ones (below). The parts:
- **The range.** Every standard $`M`$ with $`U \lt_{\mathrm{lex}} M \lt_{\mathrm{lex}} V`$ lies below some $`V_k`$ and is a
  non-increasing sum of root terms of an explicit class (pair-sequence terms, $`\upsilon`$-points, and
  segment terms whose images one level lower are again in the class). The only way into this interval is
  through the $`V[N]`$, $`N \ge 1`$ (Lemma ENT′).
- **Theorem EQB.** $`R_2^C`$ and $`R_2^S`$ agree on $`[0, \upsilon_{\omega\cdot\omega})`$. With block 0 $`= [0, \upsilon_{\omega+1}]`$
  and block $`j = (\upsilon_{\omega j+1}, \upsilon_{\omega(j+1)+1}]`$: if $`\alpha`$ is in block $`j`$ and $`\alpha \le_1 \gamma`$, then
  $`\gamma`$ is at most the top of block $`j`$, for every $`\gamma`$. The $`\lt_2`$-pairs with left end below
  $`\upsilon_{\omega\cdot\omega}`$ are exactly $`\upsilon_{\omega j} \lt_2 \upsilon_{\omega j+1}`$, $`j \ge 1`$. So Theorem B also holds
  in $`R_2^C`$.
- **The order proof.** The steps of Theorem S below $`U`$ (Pi-PAT, base change, least copy, existence,
  order) carry over. One statement had to change, and the numeric check found it: Pi-PAT (b). A
  $`\upsilon`$-point that comes from a parameter (for example $`\upsilon_2`$ inside a segment term of level
  $`\omega+1`$) need not lie in the closure of the image root; the corrected (b′) adds these points. The
  proof below $`U`$ is not affected.
- **The rule `lastt`** never acts on this range: the two functions it changes are never called there.
  Proved, and checked: the programs before and after `lastt` print the same patterns on all 107,924
  enumerated matrices (below).

The referee's minor points: (1) one step in the proof of Lemma ENT′ is false as written (for example
$`B = (0,0,0)(1,1,1)(1,1,1)`$ has $`B[N][2] = V[2]`$); the lemma still holds (only 13 standard $`B`$ are
concerned, and none has a $`B[N]`$ between $`U`$ and $`V`$ for $`N \le 40`$), and the repair is short. (2) In
Theorem EQB, the direction from $`R_2^C`$ to $`R_2^S`$ uses Claim 5.5(b), and the choice of $`\tau`$ there must be
written out. (3) Coverage of the checks only.

Checks (each run under 60 seconds, 0 failures): all 107,924 standard matrices between $`U`$ and $`V`$ with
at most 14 columns (program branches, reaches, $`\le_2`$-pairs, the three program versions equal); Pi-PAT′
at three values of $`m`$ on 12,444 segment terms (5 skipped by the time limit); $`\mathcal{T}_3`$ strictly
increasing along $`\lt_{\mathrm{lex}}`$ on 17,666 matrices; 900 random matrices with 14–40 columns. The
referee's own search: 1,860 new random standard matrices between $`U`$ and $`V`$ with 10–60 columns; the
program checks pass on all, and $`\mathcal{T}_3`$ is strictly increasing on the 1,858 distinct ones.

Not covered by this theorem: $`V`$ itself and every matrix above it. At $`\upsilon_{\omega\cdot\omega}`$ the reach
in the pattern leaves its block, and Theorem B does not describe $`R_2`$ there; see the next section. Nothing of
this is in Lean.

**Theorem S from $`V`$ up to $`V_3`$: proved on paper and refereed (with the new Lemma FRAG, refereed 2026-10).** Let
$`V_3 = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0)`$ ($`V`$ followed by `(2,0,0)`), with
$`\mathcal{T}_3(V_3) = \upsilon_{\omega^3}`$ (here $`\omega^2 = \omega\cdot\omega`$). For all standard trio matrices
$`M, M' \lt_{\mathrm{lex}} V_3`$:

```math
M \lt_{\mathrm{lex}} M' \iff \iota(\Phi_3(M)) \lt \iota(\Phi_3(M')), \qquad \iota(\Phi_3(M)) = \mathcal{T}_3(M) \lt \upsilon_{\omega^3},
```

in both $`R_2^S`$ and $`R_2^C`$; in particular $`\iota(\Phi_3(V)) = \upsilon_{\omega^2}`$. The parts:
- **The structure (Theorem B′′).** Write $`\rho_h = \upsilon_{\omega^2 h}`$ ($`h \ge 1`$; $`\rho_1`$ is the value of $`V`$).
  Below $`\upsilon_{\omega^3}`$ the $`\lt_2`$-pairs are exactly $`\upsilon_{\xi} \lt_2 \upsilon_{\xi+1}`$ for
  $`\xi = \omega^2 h + \omega j`$, $`h \ge 0`$, $`j \ge 1`$. Each $`\rho_h`$ has no $`\lt_1`$-predecessor and no
  $`\lt_2`$-successor, and $`\rho_h \le_1 \gamma`$ holds exactly for $`\gamma \in [\rho_h, \upsilon_{\omega^2 h+\omega+1} + 1]`$,
  one more than the top of its first block. Every other point is $`\le_1`$ to the same places as in $`R_1^+`$, up to
  the top of its block. All of this is proved without FRAG except the one relation
  $`\rho_h \le_1 \upsilon_{\omega^2 h+\omega+1} + 1`$; without FRAG it is proved that the reach of $`\rho_h`$ is that point
  or the one below it (Lemma TOP). With FRAG the relation is proved (Lemmas RS and RS$`^h`$).
- **Lemma FRAG.** In $`R_1^+`$, moving finitely many $`\upsilon`$-points at once, together with the parameters that
  depend on them, keeps $`0, +, \le, \le_1`$. The proof adapts Wilken's base change ([W07a] 5.3–7.10, [W07b] 4.4)
  with a map on the parameters in place of the identity. It is new. A full proof, which pushes each segment down into a
  lower one and then moves one base, was written and refereed in 2026-10 (no fatal or blocking point;
  [Trans/PoR/InaccPsi/RESTARTS.md](../../../PoR/InaccPsi/RESTARTS.md) §1).
- **Theorem EQB′′.** $`R_2^C`$ and $`R_2^S`$ agree below $`\upsilon_{\omega^3}`$; FRAG is used only for the pair above.
- **The order proof** follows the one below $`V`$, with a new last block. The only ways into the range are $`V`$
  and finitely many listed kinds of terms (Lemma ENT′′). Without FRAG it is proved that every copy of
  $`\Phi_3(M)`$ is at least $`\mathcal{T}_3(M)`$, but not that this value is reached.

The referee re-derived the new steps and read every cited proof at each step where FRAG changes the parameters.
No FATAL or BLOCKING point; FRAG was accepted at the level of a sketch. The later full proof of FRAG was refereed
with no FATAL or BLOCKING point, so the range is now proved (the order proof 1 review, FRAG 1 review).
Six minor points, among them: the choice of $`\tau`$ in Claim 5.5(b) is again not written out; a side remark
("all other pairs agree without FRAG") has a hole that a smaller sentence fixes; the move of a base with a limit
index to one with a successor index needs one line saying that it is valid in $`R_1^+`$ (not in pure $`R_2`$).

Checks (each run under 60 seconds, 0 failures): 93,270 standard matrices from $`V`$ to
$`(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(1,1,0)(2,2,1)(2,0,0)(2,0,0)`$ (value $`\upsilon_{\omega^2 \cdot 2}`$) with at most 13 columns; the program
checks on all 15,150 with at most 12 columns and a 10% sample (7,815) of those with 13; $`\mathcal{T}_3`$ increasing
on 93,293 matrices; 482 matrices of the next interval and 1,800 random ones; the reach condition on about 49,000
nodes; the step that carries patterns down on 1,833 terms. The referee's own 900 random matrices below $`V_3`$
(10–70 columns): the program checks pass on 900 of 900, and 967 matrices show 0 order violations. These checks
test the program and the translation $`\mathcal{T}_3`$, not $`R_2`$ itself.

Above $`V_3`$ the program gives $`\upsilon_{\omega^3}`$ the reach "top of its block + 2" and
$`(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(3,0,0)`$ (value $`\upsilon_{\omega^\omega}`$) the reach "top of its block +
$`\omega`$". New (2026-10, proved): the reach of $`\upsilon_{\omega^3}`$ is exactly "top + 2" in $`R_2^S`$, and a general Lemma
TOP$`_\lambda`$ bounds the reach of every restart up to the $`\omega`$-th fixed point of $`\upsilon`$ from above, "top + $`\omega`$" at
$`\upsilon_{\omega^\omega}`$ included; that these upper bounds are reached is open
([Trans/PoR/InaccPsi/RESTARTS.md](../../../PoR/InaccPsi/RESTARTS.md) §2–3).

**The sup at $`X`$ (rows 907 and 947 of [POR.md](POR.md)).** Let $`X = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(2,0,0)`$
and let $`R`$ be the sheet's reading `0 a (b ([c (e ([f g] g+e)) d] d+e d+e+a))` with point `b` (it includes the
element `d+e` that the sheet's reading implies; `por/phi3def2.py` with `lastt` prints exactly this).
Write $`P_n = \Phi_3(X[n])`$, $`\sigma = \sup_n \iota(P_n)`$ and $`\beta = \iota(R)`$. It was known that $`\sigma \le \beta`$ and
that $`\sigma = \beta`$ if and only if $`\sigma \le_1 \beta`$. Write $`R^*`$ for the least realization of $`R`$, and
$`\gamma, \delta, \varepsilon`$ for the places of `c`, `d`, `e` in it. New, proved on paper and refereed (only
minor points):
- **Lemma CG.** The pattern $`C^+`$ = $`R`$ without `b`, that is `0 a ([c (e ([f g] g+e)) d] d+e d+e+a)` with
  point `c`, generates $`R`$: its least realization is $`R^*`$ without $`\beta`$, so $`\iota(C^+) = \gamma \gt \beta`$.
- **Lemma NEST.** Every finite configuration below $`\beta`$ whose least element is indecomposable has copies
  cofinally below $`\gamma`$, inside the nested part of $`R^*`$.
- **Theorem RED.** $`\sigma = \beta`$ holds if and only if every finite configuration inside the block
  $`[\beta, \delta+\varepsilon]`$ of $`R^*`$ has cofinally many copies below $`\sigma`$. So only this block matters.
- The same three hold at $`X' = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,2,0)(2,0,0)`$.
- **Theorem L.** $`\iota(\Phi_3(X[n][k])) \lt \iota(P_n)`$ for all $`n, k`$, at $`X`$ and at $`X'`$, given the shape of
  $`\Phi_3(X[n][k])`$ (checked in 48 of 48 cases at $`X`$ and 30 of 30 at $`X'`$). So $`P_n`$ is never too small
  against its own fundamental sequence.
- At $`M_1 = (0,0,0)(1,1,1)(2,2,1)(3,1,1)(4,1,0)(5,2,1)(6,2,0)`$: $`\iota(\Phi_3(M_1)) \ge \sup_n \iota(\Phi_3(M_1[n]))`$,
  given only the shape of $`\Phi_3(M_1[n])`$.

**New at $`X`$ (proved on paper and refereed, only minor points).** Let $`\gamma_n`$ be the least place of $`P_n`$
without its point, and $`\mathrm{Cov}(\alpha)`$ the set of patterns that have a copy (a covering) below $`\alpha`$.
- **Lemma HULL.** $`\beta = \min\{b : b \lt_1 \gamma\}`$ and $`\mathrm{Cov}(\gamma) = \mathrm{Cov}(\beta)`$; the same holds for each
  $`P_n`$, above the earlier blocks.
- **Theorem RED2.** These are equivalent: $`\sigma = \beta`$; $`\sigma \lt_1 \gamma`$;
  $`\mathrm{Cov}(\gamma) = \bigcup_n \mathrm{Cov}(\gamma_n)`$; every finite closed set below $`\beta`$ has a copy below $`\sigma`$.
  So a refutation is exactly a pattern with a copy below $`\gamma`$ whose least copy reaches $`\sigma`$ or more.
- **Lemma NOC.** No copy of $`C^+`$ lies inside $`(\gamma, \delta)`$, and none has its point in $`[\sigma, \gamma)`$.
- The smallest case of the same question is $`Y_0 = (0,0,0)(1,1,1)(2,0,0)`$ with the pattern
  `0 a (b ([c c'] c'+a))`: every term of its fundamental sequence is proved to be below it; equality is open.
- HULL, RED2 and NOC hold at $`X'`$ too. At $`M_1`$, HULL holds, but RED2 does not carry over as it is.

Open: $`\sigma \le_1 \beta`$ was neither proved nor refuted. A refutation needs a pattern $`G`$ with
$`\iota(P_n) \le \iota(G) \lt \beta`$ for all $`n`$; every known way to build one uses a $`C^+`$-configuration, and then
$`\iota(G) \ge \beta`$ by Lemma CG. A proof needs a simulation of the configurations in the block of $`R^*`$ by those
in the blocks of the $`P_n`$; it is not written. Also open: equality at $`M_1`$, and whether $`P_n`$ is too large
(the same limit of a chain of blocks in both). Oracle certificates for $`R \lt C^+`$, its $`X'`$ form and the
instances of Theorem L were all replayed. The referees tested six candidate refuters (among them weakenings of $`R`$
that drop a $`C^+`$-configuration); each is below $`P_1`$ or $`P_2`$ or above $`R`$, so none lies between all $`P_n`$ and $`R`$.

**Limit-step pairs.** The order tests of [POR.md](POR.md) left 777 pairs undecided under
`por/phi3def2.py`. In 723 of them $`A = B[n]`$ with $`n \le 3`$. A certificate is a chain of Carlson's
reflection steps (Carlson 2009, Defs 9.1, 9.4, 10.1) from $`\Phi_3(B)`$, and a covering of $`\Phi_3(A)`$
into the result that maps the point of $`A`$ strictly below the point of $`B`$. That a certificate gives
$`\iota(\Phi_3(A)) \lt \iota(\Phi_3(B))`$ is proved from Carlson 2009 (Thm 14.10, Lemma 14.5, and Lemma 15.11:
in ZF every pattern is covered), given that the search program implements his definitions. 720 pairs
have a certificate, each replayed by the checker; the referee replayed all of them again. No violation
was found. The list of the other 57 was lost and was rebuilt with `lastt` (it gives the same patterns on
all seven test sets): after the same searches, 75 pairs stay open, and the 57 are most likely among them
(checked by the counts per set only). All 75 now have a certificate "<", each replayed; no violation, and a
reverse search on the last 8 found nothing. New kinds of steps were needed: one up-step with three down-steps
inside, two up-steps in a row, longer ladders of down-steps, and a "link ladder" (apply the down-step at the
last summand of each reach, from the far end back to the point). For one of the last 8 the certificate goes
through $`C = B[1]`$: $`\iota(\Phi_3(A)) \le \iota(\Phi_3(C)) \lt \iota(\Phi_3(B))`$.

For two of the last 8 the checker had rejected what the search found. The cause was two bugs of the checker,
not of the search: inside an up-step it put a repair at the wrong stage, and it treated a sum of a new node
and an old node as a copy, although Carlson 2009 Def 10.1 copies only the part below and the new part. A
corrected checker fixes both; the rule steps themselves are unchanged. It replayed again every certificate
still on file: the 67, 828 certificates of a rerun of the searches for the 720 (the 720 original files are
lost), and 69 others; no verdict changed, and 3 candidates rejected before now pass.

**Increase along fundamental sequences.** For a limit matrix $`X`$, write $`X[n]`$ for the $`n`$-th term of its
fundamental sequence. Proved on paper and refereed (no FATAL or BLOCKING point, 7 minor ones):
- **Lemma LL (link ladder).** Let $`h_0`$ be a covering of a pattern $`S`$ into $`T`$ with $`\le`$ in place of $`\lt`$ at
  the point. If $`h_0`$ sends no fact of $`S`$ to the top of the reach of the deepest link of $`T`$, then the
  down-steps at the links, from the deepest back to the point, give $`\iota(S) \lt \iota(T)`$.
- **Theorem FS.** For every limit $`X \le_{\mathrm{lex}} V`$: $`\iota(\Phi_3(X[n])) \lt \iota(\Phi_3(X[n+1]))`$.
- **Theorem V.** $`\iota(\Phi_3(V[N])) \lt \iota(\Phi_3(V))`$ for all $`N`$, so $`\iota(\Phi_3(V)) \ge \upsilon_{\omega^2}`$.

Checks on the 2,928 limits of the seven test sets, pairs $`n \le 2`$ (every certificate replayed): below $`V`$,
1,497 of 1,497 pairs are "<"; above $`V`$, 7,184 of 7,287. The referee replayed all 10,957 recorded uses of Lemma
LL, and tried to prove $`\iota(P) \lt \iota(P)`$ for 9,285 patterns: 0 hits.

**Counterexamples above $`V_3`$ (confirmed by the referee).** At 26 limits $`X`$ of the test sets,
$`\iota(\Phi_3(X[n]))`$ does not increase with $`n`$: in 41 pairs $`\Phi_3(X[n]) = \Phi_3(X[n+1])`$; in 3 pairs
$`\iota(\Phi_3(X[n+1])) \lt \iota(\Phi_3(X[n]))`$ by Lemma LL; in 14 pairs "$`\ge`$" is certified; 45 pairs stay undecided.
The same happens without `lastt`. Examples: at $`X = (0,0,0)(1,1,1)(2,2,0)(3,3,1)(4,3,0)(3,3,1)(4,3,0)`$,
$`\Phi_3(X[1]) = \Phi_3(X[2]) = \Phi_3(X[3])`$; at $`X = (0,0,0)(1,1,1)(2,2,1)(3,2,1)(2,2,1)(3,1,1)(4,2,1)(5,2,1)`$,
$`\iota(\Phi_3(X)) \lt \iota(\Phi_3(X[0]))`$. The least counterexample found is
$`(0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)`$. Below it, from $`V`$ on, the 1,114 limits of the
test sets give 3,342 pairs: all "<" except 7 undecided. The order tests of [POR.md](POR.md) did not see these
because $`X[n]`$ is not in the test sets. Which of the two patterns is wrong is open.

**Conditional or open.**
- The full equality of the Carlson–Wilken 2012 §7 remark, and the per-matrix hypotheses of the two
  further shapes for all matrices.
- $`\sigma \le_1 \beta`$ at $`X`$ and $`X'`$, that is $`\mathrm{Cov}(\gamma) = \bigcup_n \mathrm{Cov}(\gamma_n)`$; the same question at
  $`Y_0`$; equality at $`M_1`$; whether $`P_n`$ is too large.
- That $`\iota \circ \Phi_3`$ increases along every fundamental sequence from $`V`$ up to the least counterexample
  (below $`V_3`$ it follows from Theorem S), and the base case at the bad root of nested limits.
- Which pattern is wrong at the 26 counterexamples, and a repair of the rule.
- $`V_3`$ and above: that the reaches reach their upper bounds (above; "top + $`\omega`$" at $`\upsilon_{\omega^\omega}`$), and the order proof; heads with $`\Omega_2`$-level structure need
  arithmetic that the literature leaves to future work.
