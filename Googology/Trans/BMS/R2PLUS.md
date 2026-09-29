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

**Conditional or open.**
- 10 further pairs below $`\upsilon_{\omega+1}`$ (two more shapes) are decided only under a remark in
  §7 of Carlson–Wilken 2012 that is stated there without proof (and, for general bases, under a
  reading of Wilken, "Assignment of ordinals to patterns of resemblance", JSL 72, 2007, which
  was not available).
- The equivalence of $`R_2^C`$ and $`R_2^S`$ beyond $`\upsilon_{\omega+1}`$ (Theorem B in $`R_2^C`$ is only sketched).
- Beyond $`\upsilon_{\omega\cdot\omega}`$: a conjecture that each "backbone" behaves like the $`\varepsilon_0`$-multiples in
  Wilken's $`R_2`$ agrees with all 11,506 facts tested; heads with $`\Omega_2`$-level structure are
  not covered and need arithmetic that the literature leaves to future work.

