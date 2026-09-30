[← Back](POR.md) | [English](R2PLUS.md) | [Japanese](R2PLUS-ja.md)

# Theory: $`R_2^+`$ below $`\upsilon_{\omega+1}`$

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
  $`R_2^S`$ agrees with $`R_1^+`$.
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
5.7(3).) Theorem B in $`R_2^C`$ is only sketched. The referee found no gap in Theorem EQ.

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

**Theorem S on all standard matrices below $`U`$: not proved yet.** A proof for every standard trio
matrix $`M \le_{\mathrm{lex}} U`$ was written. It takes a term down one segment by replacing each nested copy
of its root by the root's $`m`$-th expansion; on values this is Wilken's base change. The referee
found no counterexample, but a gap in the step that carries patterns through this map (Theorem
Pi-PAT). Its proof says every comparison is between parameters, log summands or level nodes. That
is false in two cases: a sum step may compare with an element of the copied block, and the chosen
$`m`$ does not bound the size of the other terms (example: $`(0,0,0)(1,1,1)(1,1,0)(2,2,0)`$ with $`m = 2`$).
The repair needs two lemmas and a larger $`m`$: a sum step never reaches the copied block, and the
closure never makes a top-part diagonal longer than the term's own. Both held on all tested cases
(0 of 7,228 and 0 of 4,901). The theorem itself held on all 58,764 standard matrices $`\le U`$ with at
most 8 columns and on 3,000 random ones with 9–30 columns.

**Limit-step pairs.** The order tests of [POR.md](POR.md) left 777 pairs undecided under
`por/phi3def2.py`. In 723 of them $`A = B[n]`$ with $`n \le 3`$. A certificate is a chain of Carlson's
reflection steps (Carlson 2009, Defs 9.1, 9.4, 10.1) from $`\Phi_3(B)`$, and a covering of $`\Phi_3(A)`$
into the result that maps the point of $`A`$ strictly below the point of $`B`$. That a certificate gives
$`\iota(\Phi_3(A)) \lt \iota(\Phi_3(B))`$ is proved from Carlson 2009 (Thm 14.10, Lemma 14.5, and Lemma 15.11:
in ZF every pattern is covered), given that the search program implements his definitions. 720 pairs
have a certificate, each replayed by the checker; the referee replayed all of them again. 57 pairs
stay open in both directions. No violation was found.

**Conditional or open.**
- The full equality of the Carlson–Wilken 2012 §7 remark, and the per-matrix hypotheses of the two
  further shapes for all matrices.
- Theorem S on all standard matrices below $`U`$: the two lemmas above.
- The 57 open limit-step pairs, and a general lemma that $`\iota \circ \Phi_3`$ increases along BM4
  fundamental sequences.
- Wilken 2007 ([W07b]) Thm 2.2 is used throughout (through [W07b] Thm 5.3 and Cor 5.7). Its proof
  is in Wilken 2006, which was not available.
- The equivalence of $`R_2^C`$ and $`R_2^S`$ beyond $`\upsilon_{\omega+1}`$ (Theorem B in $`R_2^C`$ is only sketched).
- Beyond $`\upsilon_{\omega\cdot\omega}`$: a conjecture that each "backbone" behaves like the $`\varepsilon_0`$-multiples in
  Wilken's $`R_2`$ agrees with all 11,506 facts tested; heads with $`\Omega_2`$-level structure are
  not covered and need arithmetic that the literature leaves to future work.

