[← Back](README.md)

# $`\Phi`$: standard pair sequences → $`R_1^+`$-patterns (proof, part 2 of 4)

[Part 1: §0–§10](PROOF.md) | **Part 2: §11–§12** | [Part 3: §13–§14](PROOF-3.md) | [Part 4: §15–§16, References, Review history](PROOF-4.md)

## 11. Carlson–Wilken 2012

**[CW12]** T. J. Carlson, G. Wilken, <em>Normal forms for elementary patterns</em>, JSL 77
(2012) 174–194.

- §[§2](PROOF.md)–4 are free of notation. They use only [C01].
- §[§5](PROOF.md)–6 work in Wilken's $`T^\tau`$ ([W07a], [W07b], [W07c]).

### 11.1 Results recorded (CITED, with the numbers of [CW12])

**Definitions ([§2](PROOF.md)).**

- $`\mathrm{acl}(\alpha)`$ is the arithmetic closure: 0, the components $`\alpha_i`$ and the partial sums
  $`\alpha_0 + \cdots + \alpha_i`$.
- $`X`$ is **closed** iff $`\mathrm{acl}(X) = X`$. This is the same as [§1.4](PROOF.md), i.e. $`V`$'s closure under
  prefix sums and root segments.
- **Closed arithmetic embedding.** On closed sets, an embedding is determined by its
  values on the indecomposables: $`h^+(\alpha) = h(\alpha_0) + \cdots + h(\alpha_n)`$.
  - If $`h_1 \le h_2`$ on the indecomposables, then $`h_1 \le h_2`$ everywhere.
- **Covering** (p.176) is as in [C01] Def 5.1, with a closed range. **Isominimal** means
  $`\le_{\mathrm{pw}}`$-minimal among the isomorphic finite sets.
- p.176: $`\{0\} \cup I`$ is isominimal for every finite initial segment $`I`$ of the
  indecomposables. Unions of isominimal sets are isominimal.

**Revision Lemma (p.177).** Let $`X \lt Y`$ be finite, $`X \cup Y`$ closed, $`X \not\le_1 Y`$. Let $`h`$ be a covering
of $`X \cup Y`$, and $`f`$ a covering of $`X`$ with $`f \le h`$ on $`X`$. Then there is a covering $`h'`$ of $`X \cup Y`$
that extends $`f`$, agrees with $`h`$ on the indecomposables of $`Y`$, and satisfies $`h' \le h`$.

**Core Structure Theorem (p.177; from [C01] Thm 5.9, 6.11 and Def 4.12).**

1. The core is an ordinal.
2. Every pattern is isomorphic to a unique isominimal set. If $`X`$ is isominimal and $`X'`$ is
   a covering of $`X`$, then $`X \le_{\mathrm{pw}} X'`$.
3. Coverings of isominimal subsets extend to coverings of isominimal supersets.
4. If $`X`$ is isominimal, $`\alpha \in X`$, and $`\beta \in X`$ is maximal with $`\alpha \le_1 \beta`$, then $`\beta`$ is maximal among
   all $`\beta'`$ with $`\alpha \le_1 \beta'`$. In other words, **$`\mathrm{lh}(\alpha) \in X`$**.
5. If $`X`$ is isominimal, $`\alpha \in X`$ and $`\xi \le_1 \alpha`$, then $`\xi \in X`$.

**Consequences (p.179).**

- (i) If $`X \lt Y`$, $`X \not\le_1 Y`$ and $`X \cup Y`$ is isominimal, then $`X`$ is isominimal.
- (ii) Let $`X`$ be isominimal with indecomposables $`\alpha_1 \lt \cdots \lt \alpha_n`$ and $`\alpha_0 = 0`$. Then
  $`\alpha_{i+1} = \alpha_i^P \iff \mathrm{lh}(\alpha_{i+1}) = \alpha_{i+1}`$.
- (iii) $`\alpha \le_1 \alpha + 1 \iff \alpha \in L`$.

**[§3](PROOF.md), relative isominimality.**

- Def 3.1: $`\alpha`$-closed.
- Def 3.3: $`[X : Y]`$, with $`\le_1`$ made trivial outside $`Y`$.
- Def 3.5: $`\alpha`$-isomorphic and $`\alpha`$-covering.
- Lemma 3.4.
- **Def 3.6:** $`Y`$ is $`\alpha`$-isominimal if $`Y`$ is $`\le_{\mathrm{pw}}`$-minimal among its own $`\alpha`$-coverings.
- **Lemma 3.7:** $`Y`$ is 0-isominimal $`\iff`$ $`\{0\} \cup Y`$ is isominimal; relative isominimality is
  hereditary upward.
- **Lemma 3.8:** if $`Y`$ is $`\alpha`$-isominimal with least element $`\beta`$, then $`\alpha^P \lt \beta \iff \beta \lt \mathrm{lh}(\beta)`$.
- **Thm 3.9:**
  1. the union of the $`\alpha`$-isominimal sets is $`[\alpha^P, \infty)`$;
  2. each $`\alpha`$-closed $`Y`$ has a least $`\alpha`$-covering, and it is $`\alpha`$-isominimal;
  3. extension of coverings;
  4. **$`\alpha`$-isominimal sets are closed under $`\mathrm{lh}`$**;
  5. **if $`Y`$ is $`\alpha`$-isominimal, $`\beta \in Y`$ and $`\alpha \lt \xi \le_1 \beta`$, then $`\xi \in Y`$.**

**[§4](PROOF.md), uniqueness of minimal isominimal sets.**

- **Lemma 4.1 (splitting).** Let $`\alpha^P \le Y_1 \lt Y_2`$, with $`Y_1 \cup Y_2`$ $`\alpha`$-closed, $`\min Y_2`$
  indecomposable, $`\alpha' = \max Y_1`$ and $`Y_1 \not\le_1 Y_2`$. Then $`Y_1 \cup Y_2`$ is $`\alpha`$-isominimal $`\iff`$ $`Y_1`$ is
  $`\alpha`$-isominimal and $`Y_2`$ is $`\alpha'`$-isominimal.
- **Lemma 4.2.** Let $`\alpha^P \le \beta`$, and suppose <em>some</em> $`\alpha`$-isominimal set has least element $`\beta`$.
  Then an $`\alpha`$-closed $`Z`$ with least element $`\beta`$ is $`\alpha`$-isominimal $`\iff`$ $`\mathrm{lh}(\beta) \in Z`$ and
  $`Z \cap [\beta^P, \infty)`$ is $`\beta`$-isominimal.
- Lemma 4.3; Def 4.4 (block decomposition by $`\le_1`$-minimal elements).
- **Lemma 4.5 / Thm 4.6:** for every $`\beta`$ in the core there is a $`\subseteq`$-least isominimal set
  containing $`\beta`$. Relatively, $`M(\alpha, \beta)`$ is the $`\subseteq`$-least $`\alpha`$-isominimal set containing $`\beta`$.

**[§5](PROOF.md), fine localization (notation $`T^\tau`$).**

- **Def 5.1 (bar).** Let $`\alpha = \vartheta^\tau(\Delta+\eta)`$ with localization $`(\alpha_0, \ldots, \alpha_n)`$.
  - If $`\eta = \eta' + \eta_0`$ with $`\eta_0 \in P`$ ($`\eta' = 0`$ or $`\eta =_{\mathrm{NF}} \eta' + \eta_0`$), and either $`\eta_0 = 1`$ or
    $`\eta' \lt \sup_{\sigma \lt \eta'} \vartheta^\tau(\Delta+\sigma)`$, then $`\bar\alpha := \vartheta^\tau(\Delta+\eta')`$.
  - Otherwise $`\bar\alpha := \alpha_{n-1}`$.
- Lemmas 5.2–5.4; Def 5.5 (fine localization); Lemma 5.6.
- **Lemma 5.7.1:**
  - $`\bar\alpha = \max(\{\gamma \in (\tau,\alpha) \cap E : \pi^{-1}_{\gamma,\alpha}(\lambda^\tau_\gamma) \ge \lambda^\tau_\alpha\} \cup \{\tau\})`$ for $`\alpha \in E`$;
  - $`\bar\alpha = \max(\{\gamma \in (\tau,\alpha) \cap P : \lambda^\tau_\gamma \ge \lambda^\tau_\alpha\} \cup \{\tau\})`$ otherwise.
- 5.7.2–4: bar commutes with base transformation and with the translation.
- Lemma 5.8; Lemma 5.9 (fine localizations are ordered lexicographically).
- **Lemma 5.10.** Let $`\zeta \lt \alpha = \omega^\zeta \in (\tau, \tau^\infty)`$, $`\zeta =_{\mathrm{CNF}} \omega^{\zeta_1} + \cdots + \omega^{\zeta_k}`$, and let
  $`(\alpha_0, \ldots, \alpha_n)`$ be the localization of $`\alpha`$.
  1. Each $`\alpha_i`$, $`0 \lt i \lt n`$, is in the localization of $`\omega^{\zeta_1}`$.
  2. If $`\alpha_{n-1} \lt \bar\alpha`$, then $`k \gt 1`$ and $`\bar\alpha = \omega^{\zeta'}`$ with $`\zeta' = \omega^{\zeta_1} + \cdots + \omega^{\zeta_{k-1}}`$.
     **If $`\alpha \in M`$, then $`\bar\alpha = \alpha_{n-1}`$.**
  3. If $`\alpha_{n-1} = \bar\alpha`$, then either $`k = 1`$ and $`\alpha_{n-1}`$ is the immediate predecessor of
     $`\omega^{\zeta_1}`$ in its localization, or $`k = 2`$ and $`\alpha_{n-1} = \zeta_1`$.
  4. $`\zeta^\tau_\alpha = \zeta_k`$.
- Lemmas 5.11, 5.12.

**[§6](PROOF.md), arithmetic expression of normal forms.**

- The lh-characterization $`\mathrm{lh}_\tau`$ is cited there from [W07c] Def 2.32 and Thm 2.34; it is
  the same as [W07b] Def 4.1 and Thm 5.3.
- **Thm 6.1.** A $`\tau`$-relativized pattern that is isominimally realized by the identity is
  closed under $`\mathrm{lh}_\tau`$ and bar.
- **Thm 6.2.** Let $`\alpha \in (\tau, \tau^\infty)`$ and let $`P \subseteq \tau^\infty`$ be a $`\tau`$-relativized pattern. If $`\alpha \in P`$ and
  $`P`$ is closed under $`\mathrm{lh}_\tau`$ and bar, then $`P_\tau(\alpha) \subseteq P`$.
- **Cor 6.3.**
  1. $`P_\tau(\alpha)`$ is the unique $`\tau`$-relativized pattern of minimal cardinality that is
     isominimally realized by the identity and contains $`\alpha`$.
  2. $`P_\tau(\alpha)`$ is the closure of $`\{0, \tau, \alpha\}`$ under additive decomposition, $`\mathrm{lh}_\tau`$ and bar.
  3. Uniformity under base transformation.
- **Lemma 6.4:** the recursion for $`P_\tau(\alpha)`$:
  - sums: (2a);
  - $`P \setminus E`$: $`P_\tau(\alpha) = P_\tau(\bar\alpha) \cup \bigcup P_\tau(\gamma_i) \cup \{\alpha + \gamma_1 + \cdots + \gamma_i\}`$ for $`\lambda_\alpha =_{\mathrm{ANF}} \gamma_1 + \cdots + \gamma_m`$
    (2b);
  - $`E`$: $`P_\tau(\alpha) = P_\tau(\bar\alpha) \cup \bigcup_{\xi \in P_\alpha(\kappa^\alpha_{\lambda_\alpha}) \cap (\tau,\alpha)} P_\tau(\xi) \cup P_\alpha(\kappa^\alpha_{\lambda_\alpha})`$ (2c).
- **Remark 6.5:** a characterization of bar in $`R_1`$ by patterns. It uses the $`P_{\alpha_i}(\alpha)`$
  themselves.
- **[§7](PROOF.md):** $`M(\alpha, \beta) = \mathrm{acl}(P_\tau(\beta) - (\alpha+1)^P)`$ with $`\tau := \max(E_1 \cap (\alpha+2))`$.

### 11.2 Route A is now fully cited (PROVED)

**How [CW12] §6 is read for $`\tau = 1`$ (M4).** [CW12] §6 takes three notions from
[W07c] (Defs 1.1, 1.2, 2.32 and Thm 2.34), which was not obtained. For $`\tau = 1`$ they are
settled as follows.

- **"1-relativized pattern".** [CW12] p.190 says that for $`\tau = 1`$ these are the closed
  substructures of $`R_1`$, with the identity as parameter assignment and $`\le_1`$ neglected up
  to $`\tau`$. Below $`\tau = 1`$ there is only 0, so nothing is neglected. So a 1-relativized
  pattern is a finite closed substructure of $`R_1`$.
- **"Isominimally realized by the identity".** Here it means isominimal in [C01]'s sense.
  - Relativizing to $`\tau = 1`$ fixes 0 and 1.
  - But 0 and 1 are fixed by every $`\le_{\mathrm{pw}}`$-smaller isomorphic copy anyway: 0 is the least
    element, and 1 is the least nonzero indecomposable, which reaches only itself.
  - So 1-isominimality is plain isominimality.
- **$`\mathrm{lh}_\tau`$.** [CW12] p.190 says $`\mathrm{lh}_\tau`$ characterizes $`\mathrm{lh}{\restriction}(\tau, \tau^\infty)`$. For $`\tau = 1`$ this is $`\mathrm{lh}`$ on
  $`(1, \mathrm{core})`$, which is [W07b] Def 4.1 / Thm 5.3.

**Theorem 11.1 (PROVED from L, S1, 2.4, Thm VF, [CW12] Thm 6.2, Cor 6.3(1), and
Lemma 6.1).** If $`o[V_M]`$ is closed under bar, then $`\iota(\Phi(M)) = o(M)`$.

<em>Proof.</em>

0. **The case $`M = (0,0)`$ (M3).** Here $`o(M) = 1 = \tau`$, so Thm 6.2 (which needs
   $`\alpha \in (\tau, \tau^\infty)`$) does not apply. It is trivial:
   - $`V = \{(), (1)\}`$, since $`\mathrm{lh}_\Phi(1) = (1)`$ and $`(1)`$ has no anchor.
   - $`o[V] = \{0, 1\} = \{0\} \cup I`$, with $`I = \{1\}`$ an initial segment of the indecomposables. It
     is isominimal ([CW12] p.176).
   - So $`\iota(\Phi(M)) = 1 = o(M)`$.

   From here on, $`o(M) \ge 2`$, so $`o(M) \in (1, \mathrm{core})`$.
1. **$`P := o[V_M]`$ is a 1-relativized pattern.**
   - It is a closed substructure of $`R_1`$ (Lemma 5.1), contained in $`1^\infty = \mathrm{core}`$ (Lemma 1.1
     and C3).
   - It is finite (Thm VF, [§15.1](PROOF-4.md)). Finiteness is part of "pattern" ([C01] Def 4.2;
     [CW12] p.176).
2. **Closure under $`\mathrm{lh}_1`$.** $`\mathrm{lh}_1 = \mathrm{lh}`$ on $`(1, 1^\infty)`$ ([W07b] Thm 5.3), and $`V`$ is closed under
   $`\mathrm{lh}_\Phi`$. So by L, $`P`$ is closed under $`\mathrm{lh}_1`$.
3. **Applying Thm 6.2.** With the hypothesis on bar, $`P_1(o(M)) \subseteq P`$.
4. **$`P_1(o(M))`$ is isominimal** (Cor 6.3(1); see M4 above for the reading), and it
   contains $`o(M)`$.
5. **Conclusion.**
   - Lemma 6.1 with $`X = P`$ and $`Z = P_1(o(M))`$ gives $`h(o(M)) = o(M)`$. Here $`h : P \to P^*`$ is
     the isomorphism onto the isominimal copy.
   - $`P \cong \Phi(M)`$ via $`o`$ (Lemma 5.1), and the isominimal copy is unique ([CW12] Core
     Structure Theorem (2)). So $`\iota(\Phi(M)) = h(o(M)) = o(M)`$. ∎

(Step 3 is the inclusion $`\supseteq`$ of Cor VF, [§15.1](PROOF-4.md): together with Thm VF, $`o[V_M] = P_1(o(M))`$
for every $`M`$ with $`o(M) \ge 2`$.)

**Converse (PROVED from [CW12] Thm 6.1).** If $`o[V_M]`$ is isominimal, it is closed under
bar. The re-pointing test E, 1.24M checks, supports that $`o[V_M]`$ is isominimal.

So Route A needs only bar-closure (and finiteness). **Both are PROVED**: bar-closure
in §11.3 and [§14.2](PROOF-3.md), finiteness in [§15.1](PROOF-4.md). Route B (Thm 6.3 with Lemma 6.4) is not needed.

**Lean.** Theorem 11.1 is `thm111` in [Main.lean](../Main.lean), with Lemma 6.1 as `lemma61` in [Main/Iso.lean](../Main/Iso.lean) and Lemma 5.1 as `lemma51` in [Main/Pattern.lean](../Main/Pattern.lean).

### 11.3 Bar-closure for non-epsilon nodes (PROVED from R and 2.4, [CW12] Lemma 5.10, [W07a] Def 4.6, Lemmas 4.3 and 4.9)

Let $`N \in V_M`$ be a non-epsilon one-term node, $`N \ne 1`$. Put $`\alpha = o(N) = \omega^\zeta`$, where
$`\zeta = o(\log N)`$ (Lemma R). Write $`\log N = (t_1, \ldots, t_r)`$ for its root segments, so that
$`\zeta =_{\mathrm{CNF}} o(t_1) + \cdots + o(t_r)`$ (Lemma 2.2).

**(a) $`r \ge 2`$, i.e. $`\alpha \notin M`$.**

- By Fact BAR ([§15.1](PROOF-4.md), from [CW12] Lemma 5.10(2, 3) and Def 5.1), $`\bar\alpha = \omega^{\zeta'}`$ with
  $`\zeta' = o(t_1) + \cdots + o(t_{r-1})`$.
  - Fact BAR also handles case 3 with $`k = 2`$, including the sub-case $`n = 1`$, where
    $`\alpha_{n-1} = \tau = 1 \notin E`$ (M11(a)). That sub-case is excluded by a direct computation with
    Def 5.1.
- **$`(t_1, \ldots, t_{r-1}) = \mathcal{L}(N')`$ for an iterated anchor $`N' = \mathrm{anchor}^j(N)`$.**
  - $`\log N`$ is computed by CNF-adding the children one by one, with the hi-block as one
    term.
  - Later additions only remove trailing terms and append. So the surviving prefix
    $`(t_1, \ldots, t_{r-1})`$ equals the value right after the child that produced $`t_{r-1}`$ was
    added. That value is $`\mathcal{L}((0, C_1, \ldots, C_i)) = \mathcal{L}(\mathrm{anchor}^{k-i}(N))`$.
- By R, $`o(N') = \omega^{o(\mathcal{L} N')} = \omega^{\zeta'} = \bar\alpha`$, and $`N' \in V_M`$ because $`V`$ is closed under anchor.

**(b) $`r = 1`$, i.e. $`\alpha \in M`$.**

- $`\log N = (C_k)`$: the last child absorbs everything before it.
- [CW12] Lemma 5.10(2, 3) with $`k = 1`$: $`\bar\alpha = \alpha_{n-1}`$ is the immediate predecessor of
  $`o(C_k) = \omega^{\zeta_1}`$ in its localization.
- **That predecessor is $`e(C_k)`$, the largest epsilon number $`\le o(C_k)`$, or 1 if there is
  none.**
  - The elements strictly between $`\tau`$ and a non-epsilon $`\vartheta`$-term are epsilon numbers
    ([W07a] Lemma 4.9: the $`\Delta_i`$ decrease strictly, so only the last has $`\Delta = 0`$;
    Lemma 4.3: $`\Delta \gt 0 \iff`$ epsilon).
  - The greedy choice of Def 4.6 (maximal argument) cannot skip an epsilon subterm
    above the current element, since its argument is $`\ge \Omega`$. So the last one is the largest
    epsilon subterm.
  - The largest epsilon $`\le o(C_k)`$ is a subterm: follow the chain of leading
    CNF-exponent terms.
- **$`e(C_k) \in o[V_M] \cup \{1\}`$**, by induction on the size of the matrix, using
  $`\mathrm{lh}_\Phi(N) = N + \mathcal{L}(C_k) \in V`$:
  - If $`C_k`$ is epsilon, $`(C_k)`$ is a root segment of $`\mathrm{lh}_\Phi N`$. (This case does not in fact
    occur in (b): it would give $`o(N) = \omega^{o(C_k)} = o(C_k)`$, while G\* gives $`C_k \lt_p N`$.)
  - Otherwise $`e(C_k) = e(w)`$ for the leading root segment $`w`$ of $`\log C_k`$, which is in $`V`$.
    - An epsilon $`e \le \omega^g`$ satisfies $`e \le g`$, and hence $`e \le`$ the leading term of $`g`$.
  - The recursion on $`w`$:
    - if $`w`$ is epsilon, $`e(w) = o(w)`$, and $`w \in V`$ (M11(b));
    - if $`\mathrm{hi}(w) \ne \emptyset`$, $`e(w) = o((0, \mathrm{hi}(w)))`$, and $`(0, \mathrm{hi}(w))`$ is an iterated anchor of $`w`$;
    - otherwise $`e(w) = e(u_1)`$ for the first lo-child $`u_1`$ of $`w`$;
      - $`(0, [u_1])`$ is an iterated anchor of $`w`$;
      - $`\mathrm{lh}_\Phi((0, [u_1])) = (0, [u_1]) + \mathcal{L}(u_1) \in V`$ gives $`(u_1)`$ or the root segments of
        $`\log u_1`$;
      - recurse on a smaller matrix.

Numerical side check:

- absorption does occur (348 of 23,724 non-epsilon roots, e.g.
  $`(0,0)(1,1)(1,0)(2,1)(2,0)(1,0)(2,1)`$);
- the last child is absorbed in 160 cases, e.g. $`(0,0)(1,1)(1,0)(2,1)(2,0)(2,0)`$,
  $`\alpha = \omega^{\omega^{\varepsilon_0+2}} \in M`$.

This is why case (b) is needed.

**Lean.** This is `barClosure_noneps` in [Main/BarNonEps.lean](../Main/BarNonEps.lean), with no `sorry`; Fact BAR (`factBar`, `factBar1`) is proved from [CW12] Def 5.1 alone, so [CW12] Lemma 5.10 is not used.

### 11.4 Bar-closure for epsilon nodes (now PROVED given TR as $`\mathrm{Bar}_T`$, [§14.2](PROOF-3.md))

**Conjecture Bar-ε.** For an epsilon one-term node $`N = (0, C_1, \ldots, C_k)`$:
$`\mathrm{bar}(o(N)) = o(\mathrm{anchor}\, N)`$ if $`k \ge 2`$, and $`\mathrm{bar}(o(N)) = 1`$ if $`k = 1`$.

Checked by hand with [CW12] Def 5.1 and [W07a] Def 4.6 (localization):

| $`\alpha`$ | $`\vartheta`$-form | Def 5.1 case | bar | PSS |
|---|---|---|---|---|
| $`\varepsilon_1`$ | $`\vartheta(\Omega+1)`$ | $`\eta_0 = 1`$ | $`\vartheta(\Omega) = \varepsilon_0`$ | anchor ✓ |
| $`\varepsilon_\omega`$ | $`\vartheta(\Omega+\omega)`$ | $`\alpha_{n-1}`$ | 1 | $`k = 1`$ ✓ |
| $`\varepsilon_{\omega\cdot 2}`$ | $`\vartheta(\Omega+\omega\cdot 2)`$ | $`\eta' = \omega \lt \varepsilon_\omega`$ | $`\varepsilon_\omega`$ | anchor ✓ |
| $`\varepsilon_{\varepsilon_0}`$ | $`\vartheta(\Omega+\varepsilon_0)`$ | $`\alpha_{n-1}`$, localization $`(1, \alpha)`$ | **1** | $`k = 1`$ ✓ |
| $`\varphi(2,0)`$ | $`\vartheta(\Omega\cdot 2)`$ | $`\alpha_{n-1}`$ | 1 | $`k = 1`$ ✓ |
| $`\Gamma_0`$ | $`\vartheta(\Omega^2)`$ | $`\alpha_{n-1}`$ | 1 | $`k = 1`$ ✓ |
| BHO | $`\vartheta(\vartheta_1\vartheta_2 0)`$ | $`\alpha_{n-1}`$ | 1 | $`k = 1`$ ✓ |
| $`\varepsilon_{\Gamma_0+1}, \varepsilon_{\Gamma_0+2}, \varepsilon_{\Gamma_0+\omega}`$ | $`\vartheta(\Omega+\Gamma_0[+\ldots])`$ | [W21] examples | $`\Gamma_0, \varepsilon_{\Gamma_0+1}, \Gamma_0`$ | anchor ✓ |
| $`\varepsilon_{\zeta_0+\omega} = \psi_0(\Omega^2+\Omega\cdot\omega)`$ | $`\vartheta(\Omega+\zeta_0+\omega)`$ | $`\alpha_{n-1} = \zeta_0`$ | $`\zeta_0`$ | anchor $`(0,0)(1,1)(2,1)`$ ✓ |

- Bar-ε implies bar-closure for epsilon nodes, since $`V`$ is closed under anchor.
- With §11.3 and Thm 11.1, **Bar-ε + L + R + S1 + 2.4 $`\Rightarrow`$ the Main Theorem.**
- A proof of Bar-ε needs the $`\vartheta`$-form $`(\Delta, \eta)`$ of $`o(N)`$ and its localization, i.e. a coarse
  part of TR. [CW12]'s own semantic characterizations (Lemma 5.7.1 via $`\pi^{-1}`$ and $`\lambda^\tau`$;
  Remark 6.5 via the sets $`P_{\alpha_i}`$) are not free of notation.

### 11.5 What [CW12] does and does not give for the open items (superseded)

The items below were OPEN at an intermediate stage. Lemma 6.4 (epsilon) is no longer needed (Route A).
E2 and E1 are PROVED given TR ([§14.3](PROOF-3.md), §12.5).

**Lemma 6.4 (epsilon).**

- **Reduction (PROVED from [CW12] Def 3.5 and 3.6).** Let $`\alpha_N := \max(o[V_N] \cap o(N))`$ and
  $`Z_N := o[V_N] \cap [\alpha_N^P, \infty)`$. If $`Z_N`$ is $`\alpha_N`$-isominimal, then Lemma 6.4 holds for $`N`$.
  - The part of $`V_N`$ between $`\alpha_N`$ and $`\alpha_N^P`$ consists of sums of fixed elements, so $`h`$ fixes
    it.
  - With $`X :=`$ the fixed lower part, $`h`$ is a covering of $`[X : Z_N]`$ onto $`[X : h[Z_N]]`$. So
    $`h[Z_N]`$ is an $`\alpha_N`$-covering of $`Z_N`$ with $`h[Z_N] \le_{\mathrm{pw}} Z_N`$.
  - By minimality, $`h[Z_N] = Z_N`$, so $`h(o(N)) = o(N)`$.
- By Lemma 4.2, $`\alpha_N`$-isominimality of $`Z_N`$ follows from:
  - (i) $`\mathrm{lh}(o N) \in Z_N`$: true by L;
  - (ii) $`Z_N \cap [o(N)^P, \infty)`$ is $`o(N)`$-isominimal: this is recursive, and Lemma 4.1 splits
    it along blocks;
  - (iii) **$`H(\alpha_N, o(N))`$: some $`\alpha_N`$-isominimal set has least element $`o(N)`$.**
- (iii) is the irreducible, notation-free core. By Lemma 3.8 it forces
  $`o(N) \lt \mathrm{lh}(o N)`$, which holds for epsilon $`N`$. By the proof of Lemma 4.5, it says that
  $`M(\alpha_N, o(N))`$ contains nothing below $`o(N)`$. This is again "$`o(N)`$ is least of its type
  over $`\alpha_N`$", so [CW12] reformulates Lemma 6.4 but does not prove it.
- **Status at that stage: OPEN, sharpened to $`H(\alpha_N, o(N))`$. Not needed (Route B only).**

**E2 (jump minimality).**

- **Reduction (PROVED from [CW12] Thm 3.9(5) and Lemma 5.1 on the closure $`X`$ of
  $`\{N, Y\}`$).** If $`X \cap [o(N)^P, \infty)`$ is $`o(N)`$-isominimal, then E2($`Y`$) holds iff no one-term node
  $`z \in X`$ with $`N \lt z \lt Y`$ has $`Y \le_p \mathrm{lh}_\Phi(z)`$.
  - A $`\lt_1`$-predecessor $`\xi \in (o(N), o(Y))`$ of $`o(Y)`$ is $`\ge o(N)^P`$ and lies in any
    $`o(N)`$-isominimal set that contains $`o(Y)`$. So $`\xi \in X`$.
- The global quantifier of Prop 4.4 ("all nodes $`z`$") thus becomes a check on the finite
  set $`X`$. That is exactly part (i) of test J: 40,350 jumps, 0 violations.
- The hypothesis (relative isominimality of $`X`$) is of the same kind as the one in
  Lemma 6.4. **Status at that stage: OPEN, reduced. Superseded by [§14.3](PROOF-3.md).**

**E1.** [CW12] contains no new $`\mathrm{lh}`$ or $`\lambda`$ computation beyond [W07b]; its [§6](PROOF.md) uses [W07c]
Def 2.32 and Thm 2.34. **E1 needed TR at that stage. Now PROVED given TR, §12.5.**

**TR (avoiding the Buchholz $`\psi \leftrightarrow \vartheta`$ translation).**

- For **isominimality**, [CW12] §§3–4 give a notation-free induction on patterns
  (Lemmas 4.1, 4.2, Thm 3.9). It reduces everything to the statements $`H(\alpha, \beta)`$ at
  epsilon block-starts.
- Alternatively, §[§5](PROOF.md)–6 reduce it to Bar-ε.
- Both remaining statements are about where $`o(N)`$ sits among the epsilon numbers. With
  the tools available here they are checked only through the $`\vartheta`$-form of $`o(N)`$. So [CW12]
  shortens the isominimality side (non-epsilon: fully done; epsilon: one statement,
  either Bar-ε or $`H`$) but **does not remove the need for TR**. For E1, TR stays necessary.

---

## 12. The translation $`\mathcal{T}`$ into Wilken's $`\vartheta`$-terms, and the epsilon case

The implementation is [tr.py](../por/tr.py). The numerical tests and the generated data sets
were made with scripts that are not published.

### 12.1 Definition of $`\mathcal{T}`$

**Target.** Wilken's $`T^1`$ ($`\tau = 1`$; [W07a] Def 3.22).

- A term is 0, or a sum of principal terms in non-increasing order.
- A principal term is $`\vartheta_m(\xi)`$ with $`\xi \lt \Omega_{m+2}`$.
- No other normal-form condition is needed: $`\vartheta_m`$ is injective on $`T \cap \Omega_{m+2}`$
  ([W07a] Lemma 3.30).
- Comparison is by [W07a] Lemma 3.30:
  - $`\vartheta_m`$-values lie in $`[\Omega_m, \Omega_{m+1})`$;
  - $`\vartheta_m(a) \lt \vartheta_m(c) \iff (a \lt c \land a^{\star_m} \lt \vartheta_m(c)) \lor \vartheta_m(a) \le c^{\star_m}`$.
- $`\vartheta_0(0) = 1`$ and $`\vartheta_m(0) = \Omega_m`$.

**Auxiliary operations.**

- **$`\omega^Z`$ at level $`m`$** ($`Z \in [\Omega_m, \Omega_{m+1})`$, or $`Z \lt \Omega_1`$ when $`m = 0`$)
  ([WW11] Lemma 2.12(b), [CW12] Lemma 5.10):
  - $`\omega^Z = Z`$ if $`Z`$ is an epsilon number of level $`m`$, i.e. $`\vartheta_m(\Delta'+\eta')`$ with $`\Delta' \gt 0`$;
  - $`\omega^Z = \vartheta_m(\varepsilon + n - 1)`$ if $`Z = \varepsilon + n`$ with $`\varepsilon`$ such an epsilon and $`n \ge 1`$;
  - otherwise $`\omega^Z = \vartheta_m(-\Omega_m + Z)`$ (for $`m = 0`$: $`\vartheta_0(Z)`$).
- **$`\log_\omega`$** is its inverse on principal terms.

**Translation of a term $`s`$ with $`y(s) = k`$ at level $`k`$,** written $`\mathcal{T}_k(s)`$. Its value lies in
$`[\Omega_k, \Omega_{k+1})`$.

- **No children:** $`\mathcal{T}_k(s) = \vartheta_k(0)`$.
- **Non-epsilon at level $`k`$** (the last child has $`y \le k`$):
  - $`\mathcal{T}_k(s) = \omega^Z`$ at level $`k`$, where
    $`Z = [\mathcal{T}_k((k, \mathrm{hi})) \text{ if } \mathrm{hi} \ne \emptyset, \text{ else } \Omega_k \text{ (nothing when } k = 0)] + \sum_{c \text{ not hi}} \mathcal{T}_{y(c)}(c)`$.
  - Here hi = the children with $`y = k+1`$. The sum is CNF addition.
  - For $`k = 0`$ this is exactly Lemma R: $`\mathcal{T}(N) = \omega^{\mathcal{T}(\mathcal{L}N)}`$.
- **Epsilon at level $`k`$** (all children $`H_1, \ldots, H_r`$ have $`y = k+1`$; [COMB](COMB.md) T3):
  1. For each $`i`$: $`X_i := \log_\omega(\mathcal{T}_{k+1}(H_i))`$, split as $`X_i = D_i + \rho_i`$. Here $`D_i`$ is the
     part of level $`\ge k+1`$ (an $`\Omega_{k+1}`$-multiple) and $`\rho_i \lt \Omega_{k+1}`$.
  2. Let $`H_{j+1}, \ldots, H_r`$ be the maximal final run with $`D_i = D_r`$. Put $`\Delta := D_r`$ and
     $`c := \sum_{i \gt j} \omega^{\rho_i}`$.
  3. $`\eta := -1 + c`$. If $`j \gt 0`$, let $`e_p := \mathcal{T}_k((k, H_1, \ldots, H_j))`$ (the prefix; an epsilon of
     higher level). If moreover $`e_p \gt \Delta^{\star_k}`$ (the largest $`\vartheta_k`$-subterm of $`\Delta`$), put
     $`\eta := e_p + (-1 + c)`$.
  4. $`\mathcal{T}_k(s) := \vartheta_k(\Delta + \eta)`$.
- **Nodes:** $`\mathcal{T}(t_1 \cdots t_m) := \mathcal{T}_0(t_1) + \cdots + \mathcal{T}_0(t_m)`$.

**Where the rule comes from.**

- Buchholz's arguments are $`\Omega`$-exponential: $`\psi_1(x) = \Omega\cdot\omega^x = \Omega^{1+\xi}\cdot\omega^\rho`$ for $`x = \Omega\cdot\xi + \rho`$.
- Wilken's arguments are $`\Omega`$-linear and free of fixed points.
- So a child $`H`$ contributes the "monomial" $`\Omega_{k+1}^{\ldots}\cdot\omega^{\rho}`$, and the collapsed argument
  is $`\Omega_{k+1}\cdot(1 + \xi) = D`$.
- The prefix rule counts from the previous fixed point $`e_p`$. If $`e_p`$ already occurs in $`\Delta`$,
  then $`\vartheta(\Delta) \gt \Delta^\star \ge e_p`$ automatically, and $`e_p`$ is not added again.
  - This refinement was found through the one E1 mismatch of an earlier definition of $`\mathcal{T}`$:
    $`\psi_0(\Omega^\Omega + \Omega^{\Gamma_0}) = \vartheta(\Omega\cdot\Gamma_0)`$, not $`\vartheta(\Omega\cdot\Gamma_0 + \Gamma_0)`$.

**Hand values.**

| ordinal | $`\mathcal{T}`$-term |
|---|---|
| $`\omega`$ | $`\vartheta_0(1)`$ |
| $`\varepsilon_0`$ | $`\vartheta_0(\Omega)`$ |
| $`\varepsilon_1`$ | $`\vartheta_0(\Omega+1)`$ |
| $`\varepsilon_\omega`$ | $`\vartheta_0(\Omega+\omega)`$ |
| $`\zeta_0`$ | $`\vartheta_0(\Omega\cdot 2)`$ |
| $`\Gamma_0`$ | $`\vartheta_0(\vartheta_1(\Omega))`$ |
| $`\varepsilon_{\Gamma_0+1}`$ | $`\vartheta_0(\Omega+\Gamma_0)`$ |
| $`\varepsilon_{\zeta_0+\omega}`$ | $`\vartheta_0(\Omega+\zeta_0+\omega)`$ |
| $`\omega^{\varepsilon_0+1}`$ | $`\vartheta_0(\varepsilon_0)`$ |
| $`\omega^{\Gamma_0\cdot 2}`$ | $`\vartheta_0(\Gamma_0\cdot 2)`$ |
| Bachmann–Howard | $`\vartheta_0(\vartheta_1(\vartheta_2(0)))`$ |

All agree with [W21] and [CW12].

### 12.2 Numerical validation

Data sets:

- Three generated test sets (dense sets with maximal $`y = 1, 2, 3`$): all matrices reachable by $`M[n]`$ ($`n \le 3`$) and prefixes from
  $`(0,0)(1,1)(2,1)\ldots`$, $`(0,0)(1,1)(2,2)(3,2)\ldots`$, $`(0,0)(1,1)(2,2)(3,3)(4,3)\ldots`$ respectively. They
  contain 49,703, 148,436 and 32,969 matrices, with $`\le 10`$, 10 and 9 columns.
- Older generated sets, with $`y \le 5`$.

| check | what it compares | size | failures |
|---|---|---|---|
| Mono | $`\mathcal{T}`$ strictly increasing along $`\lt_p`$ (all nodes, including $`V`$-closures) | 123,432 ($`y \le 1`$) + 115,960 ($`y \le 3`$) + 348,610 (older sets, $`y \le 5`$) | 0 |
| $`\mathrm{E1}_T`$ | $`\lambda^1(\mathcal{T}N)`$ (Wilken: $`\iota`$, $`t`$, $`\zeta`$) $`= \mathcal{T}N + \sum \mathcal{T}(Y_j)`$ | 15,031 + 15,531 + 59,797 epsilon roots | 0 |
| $`\mathrm{LH}_T`$ | Wilken's $`\mathrm{lh}^1(\mathcal{T}N)`$ ([W07b] Def 4.1) $`= \mathcal{T}(\mathrm{lh}_\Phi N)`$ | 29,087 + 23,280 + 98,084 + 66,592 roots | 0 |
| CI | $`\mathcal{T}_{m-1}(\mathrm{Coll}_A s) = t(\iota(\mathcal{T}_m s))`$ | 58,132 + 63,909 + 248,247 + 179,013 | 0 |
| $`\mathrm{Bar}_T`$ | $`\mathrm{bar}(\mathcal{T}N) = \mathcal{T}(\mathrm{anchor}\, N)`$, or 1 if the root has one child | 15,031 + 15,531 epsilon roots | 0 |
| bar-closure | $`\mathrm{bar}(\mathcal{T}z) \in \mathcal{T}[V_M]`$ for every one-term $`z \in V_M`$ | 730,473 + 503,064 nodes | 0 |
| $`\mathrm{E2}_T`$ | jump inputs are $`\alpha`$-$`\le_1`$-minimal ([W07b] Cor 5.9 on $`\mathcal{T}`$-values) | 14,156 + 56,401 + 40,221 jumps | 0 |
| **Value** | poral value of $`P_1(\mathcal{T}N)`$ ([CW12] Cor 6.3, built only from $`\mathrm{lh}^1`$ and bar) = poral value of $`\Phi(N)`$ | 29,087 + 23,280 + 91,143 + 66,555 roots | **0** |

- The "Value" row is an independent check of $`\mathrm{val}\circ\mathcal{T}`$. $`P_1(\alpha)`$ is isominimally realized by
  the identity, so [poral](https://github.com/semitrivial/poral)'s value of it is $`\alpha`$ itself. Hence $`\mathrm{val}(\mathcal{T}N) = \iota(\Phi(N))`$ on 210,065
  roots.
- Warning: monotonicity alone does not certify values. An earlier definition of $`\mathcal{T}`$ (without
  the $`\Delta^\star`$ refinement) was also monotone. The E1/LH/Value checks caught the error.
- $`\mathrm{cr} \lt m`$ in [W07b] Def 4.1 does occur (125 cases at $`y \le 3`$, for example
  $`(0,0)(1,1)(2,2)(3,3)(2,2)(2,1)(3,1)(4,1)`$). In these cases $`\lambda`$'s leading term $`\delta`$ is a
  **non-jump** fold input inside the reach of an earlier jump. That jump is $`\delta_1`$ with
  $`\lambda_{\delta_1} \ge \delta`$. Def 4.1 then gives $`\mathrm{lh}(\delta_1) + \lambda`$, which is exactly $`\Phi`$'s fold. This is
  consistent with E2, which concerns jump inputs only.

### 12.3 Lemma TR (the remaining deep lemma)

**Lemma TR (PROVED in [TR](TR-2.md) §4b, via Theorem Cof and Mono\* = [TR](TR.md) Theorem M; reviewed
and accepted by the referee).** $`\mathrm{val}(\mathcal{T}(M)) = o(M)`$ for every node $`M`$.

**Reductions (PROVED).**

- **(a)** TR $`\iff`$ (Mono) $`\mathcal{T}`$ is strictly increasing along $`\lt_p`$, and (Down) its image is
  downward closed in $`T^1 \cap \Omega_1`$.
  - Both $`\mathrm{val}\circ\mathcal{T}`$ and $`o`$ are then order isomorphisms of the same well-order onto the same
    ordinal: $`T^1 \cap \Omega_1 = 1^\infty = \psi_0(\Omega_\omega)`$ (C3, Lemma 1.1). Such an isomorphism is unique.
- **(b)** TR $`\Leftarrow`$ (Mono) and (Cof): for every limit node $`M`$,
  $`\sup_n \mathrm{val}(\mathcal{T}(M[n])) = \mathrm{val}(\mathcal{T}(M))`$.
  - This is induction along $`\lt_p`$ with [COMB](COMB.md) Lemma 5 ($`o(M) = \sup o(M[n])`$; $`o(M(0,0)) = o(M) + 1`$).
  - $`\mathcal{T}`$ is trivially correct on $`(0,0)`$ and on successors, since $`\mathcal{T}`$ of a sum is the sum.
  - (Cof) is a syntactic statement. It can be checked against the fundamental sequences
    of [W24] (a Buchholz system for $`T^\tau`$ with the Bachmann property).
- **Evidence:** the Mono, $`\mathrm{E1}_T`$, $`\mathrm{LH}_T`$ and Value rows above.
- **What a proof needs.** Either (Down), by an explicit inverse $`\mathcal{T}^{-1}`$ with standardness of
  its values (this meets [COMB](COMB.md) Lemma C again), or (Cof), by a case analysis of the PSS
  expansion $`M[n]`$ against the fundamental sequences of [W24].
  - The Buchholz $`\psi \leftrightarrow \vartheta`$ literature translation is not needed; [WW11] p.117 says it does
    not exist.

### 12.4 Lemma CI (Coll ↔ ι)

**CI (outline; now PROVED in [§13.2](PROOF-3.md) with [§14.1](PROOF-3.md) and M5 of [§15.2](PROOF-4.md); 549,301 checks,
0 failures).** Let $`N = (0, A)`$ be epsilon,
$`\alpha := \mathcal{T}(N) = \vartheta_0(\Delta+\eta)`$, and let $`s`$ be a term with $`y(s) = m \ge 1`$ that $`\mathrm{Coll}_A`$ actually reaches.
That is, $`s`$ is in $`W`$'s subtree through ancestors with $`y \ge 1`$, or $`s`$ is a truncation
$`W|_i = (1, D_1 \ldots D_i)`$. Then ([W07a] Def 6.2 and Def 7.1):

```math
\mathcal{T}_{m-1}(\mathrm{Coll}_A(s)) = t^\alpha_\tau(\iota_{1,\alpha}(\mathcal{T}_m(s)))
```

The restriction matters: terms below a $`y = 0`$ node are never collapsed. Including them
gave 66 false mismatches.

<em>Outline (structural induction on $`s`$).</em>

- **$`m \ge 2`$.** $`\mathrm{Coll}_A`$ lowers $`y`$ by one and applies itself to the children. $`\iota`$ lowers the
  levels $`\ge 2`$ by one, and $`t`$ is homomorphic on levels $`\ge 1`$. The rules of $`\mathcal{T}_k`$ are uniform in
  $`k \ge 1`$ ($`\vartheta_k(0) \mapsto \vartheta_{k-1}(0)`$, $`\omega^\cdot`$ at level $`k \mapsto \omega^\cdot`$ at level $`k-1`$). [W07a] Lemma 7.2(a),
  (b) says that $`\iota`$ keeps the order and maps $`P_{m+1}`$ onto $`P_m`$, so the grouping in step 2
  and the test "$`e_p \gt \Delta^\star`$" are preserved.
- **$`m = 1`$, $`s`$ non-epsilon at level 1.**
  - $`\iota(\mathcal{T}_1(s)) = \vartheta^\alpha(\iota x)`$, with no level-1 part in $`T^\alpha`$ ($`\Gamma = 0`$).
  - So $`t`$ gives $`\vartheta_0(\alpha + (-1 + t \iota x))`$.
  - $`\mathrm{Coll}_A(s)`$ is the blob $`(0, A + \mathrm{Coll}(\text{children}))`$. Its $`\mathcal{L}`$ is
    $`(0, A \mathbin{+\!\!+} \mathrm{Coll}(D\text{'s})) + \mathrm{Coll}(\text{other children})`$. By induction its value is $`\omega^{t \iota(Z)}`$
    with $`\iota(\Omega) = \alpha`$. This matches up to the $`\varepsilon+n`$ and $`-1`$ adjustments.
- **$`m = 1`$, $`s`$ epsilon at level 1.**
  - The blob is epsilon, with children $`A \mathbin{+\!\!+} \mathrm{Coll}(D\text{'s})`$.
  - Its last run consists of $`\mathrm{Coll}(D)`$'s (their $`D`$-parts contain $`\alpha`$, while the $`H`$'s in $`A`$ do
    not). So $`\Delta_{\mathrm{blob}} = t(\iota(\Delta_s))`$ and $`c_{\mathrm{blob}} = \iota(c_s)`$.
  - [W07a] Def 6.2 splits into three cases:
    - $`\Gamma = 0`$: $`t`$ gives $`\vartheta(\alpha + \rho)`$;
    - $`\Gamma \gt 0`$ without a $`\vartheta^\alpha`$-subterm: $`t`$ gives $`\vartheta(\Gamma^t + \alpha + \rho^t)`$;
    - $`\Gamma`$ with a $`\vartheta^\alpha`$-subterm: $`t`$ gives $`\vartheta(\Gamma^t + \rho^t)`$.
  - These match $`\mathcal{T}`$'s prefix rule exactly: the prefix of the blob is $`A`$, so $`e_p = \alpha`$. It is
    added iff $`\alpha \gt \Delta^{\star}_{\mathrm{blob}}`$, iff $`\Gamma`$ contains no $`\vartheta^\alpha`$-subterm.
  - When the level-1 prefix is non-empty, $`e_p = t \iota(\mathcal{T}_1 \text{ of the truncation})`$, by induction.
- **What is left for a full proof:**
  - the finitely many adjustment cases ($`\varepsilon+n`$ in $`\omega^\cdot`$, $`-1+`$ at level 0, $`\Omega_0 = 1`$);
  - the claim that $`\mathrm{Coll}(D)`$-parts are never grouped with the $`H`$'s of $`A`$.

### 12.5 E1

**$`\mathrm{E1}_T`$ (PROVED from CI, Mono, and fact NS below).** For epsilon $`N`$, with $`\alpha = \mathcal{T}(N)`$
($`T^1`$ ordinal sum):

```math
\lambda^1(\alpha) = \alpha + \mathcal{T}(Y_1) + \cdots + \mathcal{T}(Y_n)
```

<em>Proof.</em> Write $`W = (1, D_1 \ldots D_p, E_1 \ldots E_q)`$. This order is [COMB](COMB.md) T4.

- **Case $`q = 0`$.**
  - $`\mathcal{T}_1(W)`$ is a level-1 epsilon number, so $`\Delta = \mathcal{T}_1(W)`$ and $`\rho_W = 0`$.
  - By CI with $`s = W = W|_p`$: $`t \iota(\Delta) = \mathcal{T}(Y_p)`$.
  - $`\zeta_\alpha = 0`$. Either $`\eta`$'s last term is 1, or $`\eta = e_p`$ is a sup-point ([W07a] Lemma 4.4:
    $`e_p`$ has higher level and $`e_p \gt \Delta^\star`$).
  - On the right: $`\alpha \lt \mathcal{T}(Y_1) \lt \cdots \lt \mathcal{T}(Y_p)`$ are additive principal numbers (Mono). So the
    sum is $`\mathcal{T}(Y_p)`$.
- **Case $`q \gt 0`$.**
  - $`\mathcal{T}_1(W) = \omega^Z`$ with $`Z = Z_D + \sum_j \mathcal{T}(E_j)`$, where $`Z_D = \mathcal{T}_1(W|_p)`$ if $`p \gt 0`$, else $`\Omega`$.
  - $`\log_\omega \circ \omega^\cdot = \mathrm{id}`$. So $`\Delta = Z_D + \sum_{y(E)=1} \mathcal{T}_1(E_j)`$ and $`\rho_W = \sum_{y(E)=0} \mathcal{T}_0(E_j)`$.
  - $`t \iota`$ is additive, and $`t \iota(\Omega) = \alpha`$. By CI:
    $`t \iota(\Delta) = [\alpha \text{ or } \mathcal{T}(Y_p)] + \sum_{y(E)=1} \mathcal{T}(\mathrm{Coll}_A E_j)`$.
  - $`\zeta_\alpha = \mathrm{logend}(\eta) = \rho_W`$. The last ANF term of $`\eta`$ is $`\omega^{\rho_W}`$, or 1 if $`\rho_W = 0`$.
  - The right-hand side is the same sum: the $`Y_i`$ absorb one another, and $`\mathrm{Coll}_A(E) = E`$
    for $`y(E) = 0`$.
- **Fact NS** (standardness; numerically implied): $`\eta`$ is a sup-point only when $`\rho_W = 0`$.
  - The non-standard $`(0,0)(1,1)(2,0)(3,1)(4,1)`$ would violate it, since its $`\eta = \zeta_0`$ is a
    sup-point with $`\rho_W = \zeta_0`$.
  - It belongs with [COMB](COMB.md)'s standardness lemmas. ∎

**E1 (PROVED from $`\mathrm{E1}_T`$, TR and [W07b] Thm 5.3).** $`\lambda_{o(N)} = \lambda^1_{\mathcal{T}(N)}`$, because
$`\mathrm{val}(\mathcal{T}N) = o(N)`$. Then $`\mathrm{E1}_T`$ gives E1.

**Lean.** E1 is stated as `E1` in [Main/E12.lean](../Main/E12.lean) and left as `sorry`: CI, $`\iota_{1,\alpha}`$, $`t^\alpha_\tau`$ and [W07b] Thm 5.3 are not formalized.

### 12.6 E2, and the circularity

**E2 (PROVED from $`\mathrm{E2}_T`$, TR, [W07b] Thm 5.3 and Cor 5.9).** By Cor 5.9, the greatest
$`\lt_1`$-predecessor of $`\beta`$ in $`(\alpha, \beta)`$ is $`\beta_i`$ for the largest $`i`$ with $`\lambda_{\beta_i} \ge \beta`$, where the $`\beta_i`$
are from the $`\alpha`$-localization of $`\beta`$. $`\mathrm{E2}_T`$ says no such $`i`$ exists for $`\beta = \mathcal{T}(Y)`$, $`Y`$ a jump
input. $`\mathrm{E2}_T`$ is a syntactic statement about $`\mathcal{T}`$-terms (110,778 checks).

**The circularity is gone.**

- E2 is now decided on the $`\vartheta`$-side and needs no L for intermediate nodes. Prop 4.4 is no
  longer needed.
- Prop 4.3 (L for epsilon $`N`$ from E1, E2 and T) is an induction on the $`\mathrm{lh}_\Phi`$ call tree.
  That tree is finite by [COMB](COMB.md) T, whose measure is the provenance depth
  $`\lt \mathrm{height}(W_N)`$.
- So **L $`\Leftarrow`$ TR + $`\mathrm{E1}_T`$ + $`\mathrm{E2}_T`$** (with [COMB](COMB.md) T).
- Equivalently, given TR, **L $`\iff`$ $`\mathrm{LH}_T`$** ($`\mathrm{lh}^1\circ\mathcal{T} = \mathcal{T}\circ\mathrm{lh}_\Phi`$) by [W07b] Thm 5.3. $`\mathrm{LH}_T`$ is
  checked directly on 217,043 roots.

### 12.7 Bar-ε and isominimality

**$`\mathrm{Bar}_T`$ (outline; now PROVED in [§13.3](PROOF-3.md) and [§14.2](PROOF-3.md); 30,562 checks).** For epsilon $`N`$: $`\mathrm{bar}(\mathcal{T}N) = \mathcal{T}(\mathrm{anchor}\, N)`$ if the
root has $`\ge 2`$ children, else 1 ([CW12] Def 5.1).

<em>Outline.</em>

- **$`W`$ shares its run with $`H_{k-1}`$.**
  - $`c = c_a + \omega^{\rho_W}`$ without absorption. Siblings do not increase ([COMB](COMB.md) I3), and
    within a run $`\rho`$ does not increase.
  - So $`\eta'`$ ($`\eta`$ minus its last term) is the $`\eta`$ of the anchor, and $`\eta_0 = \omega^{\rho_W}`$.
  - Either $`\eta_0 = 1`$, or $`\eta'`$ is not a sup-point. (A sup-point would force $`c_a = 1`$ and hence
    $`\rho_W = 0`$.)
  - Def 5.1, first case: $`\mathrm{bar} = \vartheta(\Delta + \eta') = \mathcal{T}(\mathrm{anchor})`$.
- **$`W`$ alone in its run.** Here $`e_p = \mathcal{T}(\mathrm{anchor})`$.
  - If $`e_p \gt \Delta^\star`$: $`\eta = e_p + (-1 + \omega^{\rho_W})`$ (possibly absorbed). Def 5.1 falls into the
    second case, because $`\eta' = e_p`$ is a sup-point, or $`\eta = e_p`$, or $`\eta`$ is a single term. Then
    $`\mathrm{bar} = \alpha_{n-1}`$. By [W07a] Lemma 6.5 ($`\alpha \in (e_p, e_p^+)`$), the localization of $`\alpha`$ is that
    of $`e_p`$ followed by $`\alpha`$, so $`\alpha_{n-1} = e_p`$.
  - If $`e_p \le \Delta^\star`$: $`\eta = -1 + \omega^{\rho_W}`$, and again $`\alpha_{n-1} = e_p`$. Example:
    $`\psi_0(\Omega^\Omega + \Omega^{\Gamma_0}) = \vartheta(\vartheta_1(\Gamma_0))`$ has localization $`(1, \Gamma_0, \alpha)`$.
- **$`k = 1`$.** No prefix, and $`\mathrm{bar} = \alpha_{n-1} = 1`$.
- **Left open:** the membership $`\alpha \in (e_p, e_p^+)`$, and the localization claim in the case
  $`e_p \le \Delta^\star`$.

**Isominimality, Route A (PROVED from TR, L, $`\text{bar-closure}_T`$, [CW12] Thm 6.2 and
Cor 6.3).** bar is an operation on ordinals. So under TR, $`\mathrm{bar}(o(x)) = \mathrm{val}(\mathrm{bar}(\mathcal{T}x))`$, and
closure of $`o[V_M]`$ under bar is the syntactic $`\text{bar-closure}_T`$ (checked on 1,233,537 nodes).
Then Thm 11.1 applies.

For non-epsilon nodes, bar-closure is already PROVED (§11.3). For epsilon nodes it
follows from $`\mathrm{Bar}_T`$, since $`V`$ is closed under anchor.

### 12.8 What remained open at an intermediate stage (superseded; the current status is [§0](PROOF.md))

Every item below is now PROVED: TR in [TR](TR.md); CI, $`\mathrm{E2}_T`$, $`\mathrm{Bar}_T`$ and NS in [§13](PROOF-3.md)–[§14](PROOF-3.md); Lemma C
in [COMB](COMB.md); finiteness of $`V_M`$ in [§15.1](PROOF-4.md).

**The list at that stage. The Main Theorem follows from:**

- **TR** ($`\mathrm{val}\circ\mathcal{T} = o`$): OPEN, deep; strong evidence (§12.2 "Value");
- the syntactic lemmas **CI** (hence $`\mathrm{E1}_T`$), **$`\mathrm{E2}_T`$** (or $`\mathrm{LH}_T`$ directly) and **$`\mathrm{Bar}_T`$**:
  OPEN, with proof outlines; identities about explicit term maps, each checked on $`10^4`$–$`10^6`$
  instances;
- **NS** (one standardness fact);
- [COMB](COMB.md) (S1, R, Lemma 6, T PROVED; Lemma 2.4 except its epsilon case, which is Lemma C,
  OPEN);
- the cited results of [C01], [W07a], [W07b], [WW11] and [CW12].

The syntactic lemmas are statements about finite term trees. They are natural targets
for a Lean formalization by structural induction.

---

[Part 1: §0–§10](PROOF.md) | **Part 2: §11–§12** | [Part 3: §13–§14](PROOF-3.md) | [Part 4: §15–§16, References, Review history](PROOF-4.md)
