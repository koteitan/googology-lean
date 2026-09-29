[← Back](README.md)

# $`\Phi`$: standard pair sequences → $`R_1^+`$-patterns (proof)

**Part 1: §0–§10** | [Part 2: §11–§12](PROOF-2.md) | [Part 3: §13–§14](PROOF-3.md) | [Part 4: §15–§16, References, Review history](PROOF-4.md)

The proof is split into four files, because GitHub renders only a limited amount of math on one page. Sections and lemmas are numbered through all four files, and a reference to a section in another file is a link.

Status labels:

- **PROVED**: the full argument is given here. It may use lemmas labelled CITED or OPEN;
  those are then named.
- **LEAN**: already proved in a Lean library (file and theorem name given).
- **CITED**: from the literature. The paper, the number, and the statement are given.
- **OPEN**: not proved. What is missing and the numerical evidence are given.

The numerical checks were made with scripts that are not published; only
[phi.py](../por/phi.py), [pss.py](../por/pss.py) and [tr.py](../por/tr.py) are in this
repository. The checks are:

- test E (re-pointing);
- test M (maximality of the reach);
- test R (the reading lemma);
- test J (E2, semantic, [poral](https://github.com/semitrivial/poral) as oracle), with
  controls.

---

## 0. Summary (this section is the authoritative status)

**Main Theorem.** For every standard pair sequence $`M`$:
$`\iota(\Phi(M))=o(M):=\mathrm{pairOrdL}(M)=1+\mathrm{val}(\mathrm{pairTerm}\ M)`$.

Both halves of the conjecture follow from it (Cor 7.2): $`\Phi`$ keeps the order, and its
image is $`\mathrm{Core}(R_1^+)\setminus \{0\}`$.

**Status.** Given [TR](TR.md) and [COMB](COMB.md), every step of the Main Theorem is PROVED.
There is no OPEN item inside this file.

- [TR](TR.md): §2 there proves Mono\* (Theorem M, every level $`k`$), and §4b proves TR
  ($`\mathrm{val} \circ \mathcal{T}=o`$, via Theorem Cof). [TR](TR.md) was reviewed and
  accepted (see Review history).
- [COMB](COMB.md) was reviewed and accepted (see Review history).
- [COMB](COMB.md): S1, Lemma R, Lemmas 1–6, 10, T, Theorem SC, Lemma C, Lemma 2.4.
- Outside assumption (M13): the Lean constant `Ord.psi (Ord.Omega ω) 0` is Buchholz's
  $`\psi_0(\Omega_\omega)`$. This is needed only to read Cor 7.2(b) as
  "$`\mathrm{Core} \setminus \{0\}`$" (§1.4, C3).

**The chain (Route A).**

| step | statement | where | depends on |
|---|---|---|---|
| 1 | $`o`$ is an order isomorphism from the nodes onto $`\psi_0(\Omega_\omega)`$ | Lemma 1.1 | LEAN |
| 2 | $`o`$ turns root segments into the ANF; closed sets | Lemma 2.2, Cor 2.3 | S1 [COMB](COMB.md) |
| 3 | anchors and $`\mathrm{lh}_\Phi`$ values are standard | Lemma 2.4 | [COMB](COMB.md) |
| 4 | reach lemma L: $`\mathrm{lh}(o N)=o(\mathrm{lh}_\Phi N)`$ | §4.2, Lemma 4.2, Prop 4.3 | R [COMB](COMB.md), T [COMB](COMB.md), E1 ([§12.5](PROOF-2.md)), E2 ([§14.3](PROOF-3.md)), [W07b] |
| 5 | **$`V_M`$ is finite; in fact $`o[V_M]=P_1(o(M))`$** | **Thm VF, Cor VF ([§15.1](PROOF-4.md))** | L, $`\mathrm{Bar}_T`$, R, SC, [CW12] Cor 6.3, Lemma 5.10 |
| 6 | $`o{\restriction}V_M`$ is an isomorphism of $`\Phi(M)`$ onto a closed pattern | Lemma 5.1 | 2, 3, 4, 5 |
| 7 | $`o[V_M]`$ is closed under bar | [§11.3](PROOF-2.md) (non-epsilon), $`\mathrm{Bar}_T`$ [§14.2](PROOF-3.md) (epsilon) | R, TR, Mono\* |
| 8 | $`\iota(\Phi(M))=o(M)`$ | Thm 11.1 | [CW12] Thm 6.2, Cor 6.3, Lemma 6.1 |
| 9 | both halves of the conjecture | Thm 7.1, Cor 7.2 | 8, C3 |

**The syntactic lemmas about $`\mathcal{T}`$ used in steps 4 and 7** (all PROVED here, from
Mono\* and [COMB](COMB.md); [§13](PROOF-3.md)–[§14](PROOF-3.md)): S-eps, $`\iota`$-exp, NS, CI (with ND, LT),
$`\mathrm{E1}_T`$, CL, EL, FD, LV, LOC′, LOC″, $`\mathrm{Bar}_T`$, PL.

**Not needed** (kept only for the record):

- Route B: Thm 6.3 and Lemma 6.4 (§6). Lemma 6.4 for epsilon $`N`$ is not proved, and
  nothing uses it.
- Prop 4.4 and test J (§4.7), superseded by the $`\vartheta`$-side proof of E2 ([§14.3](PROOF-3.md)).
- The earlier "OPEN" lists in §10, [§11.4](PROOF-2.md), [§11.5](PROOF-2.md) and [§12.8](PROOF-2.md). They are marked as superseded
  where they stand.

**Numerical evidence for step 5.** A numerical check compares $`\mathcal{T}[V_M]`$ with
$`P_1(\mathcal{T}M)`$ as sets of $`T^1`$-terms. They are equal on all 231,105 matrices of
three generated test sets (dense sets with maximal $`y=1,2,3`$) (max
$`\lvert V_M \rvert=19`$). A second check verifies the structural claim of Lemma H on
7,513 absorbed cases, with 0 failures.

---

## 1. Objects and cited foundations

### 1.1 Matrices

- A matrix is a list of columns $`(x,y)`$. The row-0 parent, the root, and the term
  $`T(i)=(y,\text{children})`$ are as in [POR.md](../POR.md) §2.
- A matrix $`M`$ is the concatenation of its root segments $`t_1 \cdots t_m`$. A node is
  written as the tuple of its root terms.
- $`\mathrm{Std}`$ is `CTPS`. $`R`$ is the set of one-root members of $`\mathrm{Std}`$.
- $`\lt_p`$ is the lexicographic order (`Bijectivity.ltPS`).
- The nodes are $`\mathrm{Std} \cup \{\emptyset\}`$. $`\emptyset=()`$ is the node 0, and
  $`(1)=(0,0)`$ is the node 1.
- $`\mathrm{add}`$ is CNF addition of tuples: drop the trailing terms of the left tuple that
  are smaller than the first term of the right tuple, then append.
- For a one-root term $`N=(0,(C_1,\ldots,C_k))`$:
  - $`\mathrm{hi}(N)`$ are its children with $`y \ge 1`$, and $`\mathrm{lo}(N)`$ its children
    with $`y=0`$;
  - $`N`$ is **epsilon** iff $`k \ge 1`$ and $`y(C_k)\ge 1`$;
  - $`\mathrm{anchor}(N)=(0,(C_1,\ldots,C_{k-1}))`$ for $`k \ge 2`$;
  - $`\log`$, $`\lambda`$, $`\mathrm{Coll}_A`$, $`\oplus`$ and $`\mathrm{lh}_\Phi`$ are as in
    [POR.md](../POR.md) §3 and [phi.py](../por/phi.py).
- For $`N \in R`$ put $`\mathcal{L}(N):=(N)`$ if $`N`$ is epsilon, and
  $`\mathcal{L}(N):=\log(N)`$ otherwise.

  Here $`\log(N)=\mathrm{add}((0,\mathrm{hi}\ N))+\mathrm{lo}(N)`$, computed with
  **CNF addition**, so it may absorb terms. By definition $`\lambda(N)=\mathcal{L}(C_k)`$,
  where $`C_k`$ is read as a root term.

### 1.2 The ordinal of a matrix

$`o(\emptyset)=0`$, and $`o(M)=\mathrm{pairOrdL}(M)`$ for $`M \in \mathrm{Std}`$.

**Lemma 1.1 (LEAN, [Rank.lean](../Rank.lean)).**

- (a) `ltPS_iff_pairOrdL_lt`: $`M \lt_p N \iff o(M)\lt o(N)`$.
- (b) `range_pairOrd`, `val_psiOmegaOmega`: the image of $`o`$ is
  $`[0,\psi_0(\Omega_\omega))`$.
- (c) `typein_pairLt`: $`o(M)=\mathrm{otp}\{N:N \lt_p M\}`$.
- `isWellOrder_pairLt`: $`\lt_p`$ is a well-order on the nodes.

### 1.3 $`R_1^+`$ and $`\le_1`$

$`R_1=(\mathrm{On}; 0,+,\le,\le_1)`$. Here $`+`$ is the graph of ordinal addition, and
$`\alpha \le_1 \beta`$ iff $`(\alpha; 0,+,\le,\le_1)`$ is a $`\Sigma_1`$-elementary
substructure of $`(\beta; 0,+,\le,\le_1)`$. This is [C01] §1 and [W07b] §1. Carlson calls
this structure $`R_1`$; it is the $`R_1^+`$ of the conjecture.

$`\mathrm{lh}(\alpha):=\max\{\beta:\alpha \le_1 \beta\}`$ if the maximum exists, and
$`\infty`$ otherwise [W07b, Def 3.1].

**CITED [W07b, Lemma 2.1]** (proved in [W06] §3). $`\le_1`$ is a partial order, and:

- (a) if $`\alpha \le_1 \beta`$ for every $`\beta \in[\alpha,\lambda)`$, with $`\lambda`$ a
  limit greater than $`\alpha`$, then $`\alpha \lt_1 \lambda`$;
- (b) if $`\alpha \le \beta \le \gamma`$ and $`\alpha \le_1 \gamma`$, then
  $`\alpha \le_1 \beta`$;
- (c) $`\{\beta:\alpha \le_1 \beta\}`$ is an interval.

**CITED [W07b, Thm 2.2]** (proved in [W06] §3). For $`\alpha \in \mathrm{On}`$ and
$`\xi \in(0,\alpha]`$:

```math
\alpha \le_1 \alpha + \xi \iff \alpha = \omega^{\alpha'} \text{ for some } \alpha' \text{ with } \mathrm{logend}(\alpha') \ge \xi.
```

Here $`\mathrm{logend}(\alpha')`$ is the exponent of the last term of the Cantor normal form
of $`\alpha'`$. Consequences stated in [W07b] §2:

- $`\alpha \lt_1 \beta`$ for some $`\beta \gt \alpha`$ iff $`\alpha \in L`$, the limits of
  additive principal numbers;
- $`\alpha \le_1 \alpha \cdot 2`$ iff $`\alpha \in E`$, the epsilon numbers.

**CITED: the finite-set criterion** ([W07b] proof of Claim 5.5(a); [A15, Lemma 4];
[W21, Prop 1.6]). $`\alpha \le_1 \beta`$ iff for all finite $`X \subseteq \alpha`$ and
$`Y \subseteq[\alpha,\beta)`$ there is $`\tilde Y`$ with $`X \lt \tilde Y \lt \alpha`$ and
$`X \cup \tilde Y \cong X \cup Y`$, the isomorphism fixing $`X`$.

**Lemma 3.1 (PROVED).** Now partly covered by the citation above:

- (c) $`\alpha \lt_1 \beta`$ implies $`\alpha \in P`$;
- (d) 0 and 1 reach only themselves.

### 1.4 Closed sets, isominimality, core (all from [C01] §1–§5)

- **Closed** ([C01] p.20): a substructure $`A`$ of $`R_1`$ is closed if $`0 \in A`$ and,
  whenever $`\xi_1+\cdots+\xi_m \in A`$ with $`\xi_1 \ge \cdots \ge \xi_m`$
  indecomposable, also $`\xi_i \in A`$ and $`\xi_1+\cdots+\xi_i \in A`$ for all $`i`$.
  This is exactly closure under root segments and prefix sums (Lemma 2.2).
- **Isominimal** ([C01] p.25, §3): a finite substructure $`B`$ is isominimal if $`B=C`$
  for every substructure $`C \cong B`$ with $`C \le_{\mathrm{pw}} B`$.
- The **core** is the union of the isominimal substructures.
- **Covering** ([C01, Def 5.1]; [W07b, Def 5.1]): an injection that keeps $`\le`$ and $`+`$
  and keeps $`\le_1`$ in the direction $`a \le_1 b \Rightarrow h(a)\le_1 h(b)`$. An
  isomorphic copy is a special case.
- A pattern is **covered** if it has a covering into $`R_1`$.

**C1 (CITED [C01, Thm 5.9 (1), (2), (4)] and the remark after it).** For every covered
pattern $`P`$ there is a substructure $`P^*`$ of $`R_1`$ such that:

- (1) $`P^* \cong P`$;
- (2) $`P^*`$ is closed;
- (4) $`P^* \le_{\mathrm{pw}} Q`$ for every substructure $`Q`$ of $`R_1`$ that is a cover of
  $`P`$.

Hence $`P^*`$ is isominimal. $`\iota(P)`$ is the element of $`P^*`$ at the point of $`P`$.

**C2 (CITED [C01] proof of Thm 5.12; [C09, Lemma 2.7]).** A finite union of isominimal sets
is isominimal.

**C3 (CITED).**
$`\mathrm{Core}(R_1)=\min\{\alpha:\alpha \lt_1 \infty\}=T^1 \cap \Omega_1=\psi_0(\Omega_\omega)`$.
Sources:

- [C01, Thm 5.12]: the core is the least $`\kappa`$ with $`\kappa \le_1 \infty`$.
- [W07b, Cor 5.10] with $`\tau=1`$:
  $`T^1 \cap \Omega_1=\min\{\alpha \gt 1:\alpha \lt_1 \infty\}`$.
- [W07a, Thm 3.23, Cor 3.24]:
  $`T^1 \cap \Omega_1=\sup_n \vartheta_0(\cdots\vartheta_n(0)\cdots)`$, which is
  $`\lvert \Pi^1_1\text{-}\mathrm{CA}_0 \rvert`$.
- Buchholz's $`\psi_0(\Omega_\omega)`$ is also $`\lvert \Pi^1_1\text{-}\mathrm{CA}_0 \rvert`$
  ([B86]); this is how the two sides are identified.
- **Outside assumption (M13).** Lemma 1.1(b) is about the Lean value
  `Ord.psi (Ord.Omega ω) 0`. Reading it as Buchholz's $`\psi_0(\Omega_\omega)`$ of [B86]
  assumes that the Lean definition of `Ord.psi` is Buchholz's $`\psi`$. This file does not
  check that. Only Cor 7.2(b)'s phrase "$`=\mathrm{Core} \setminus \{0\}`$" depends on it.
  Cor 7.2(a) and the Main Theorem do not.

**Corollary 1.2 (PROVED).** For $`\alpha \lt \psi_0(\Omega_\omega)`$,
$`\mathrm{lh}(\alpha)\lt \infty`$ and
$`\{\beta:\alpha \le_1 \beta\}=[\alpha,\mathrm{lh}\ \alpha]`$. The proof is by C3 and
Lemma 2.1.

---

## 2. Standardness and additivity

**S1.** A non-empty column list is in $`\mathrm{Std}`$ iff:

- (a) its root segments are in $`R`$,
- (b) the root segments do not increase, and
- (c) (converse direction) every concatenation of $`R`$-elements that do not increase is in
  $`\mathrm{Std}`$.

Status: **PROVED** in [COMB](COMB.md) §4 (S1 (a), (b), (c)), using [COMB](COMB.md)
Lemmas 1–3. The earlier notes below are kept for the record.

- (a) ⇒: **LEAN** in [pss-proof](https://github.com/koteitan/pss-proof):
  `PSS.SkTPS_P_components` says every component of `P M` of a fixed-rank standard sequence
  is again of that rank. `P` splits $`M`$ at the row-0 roots (`Pcut`). Together with
  `SkTPS_STPS`, and after shifting the component to start at $`(0,0)`$, this gives (a).
  - Caveat: the shift from a component to a `CTPS` matrix. [COMB](COMB.md) §9.1 shows it is
    vacuous: roots are $`(0,0)`$ ([COMB](COMB.md) T1), and `P` gives the root segments
    literally ([COMB](COMB.md) Lemma 2).
- (b): only a row-1 tie-break is in [pss-proof](https://github.com/koteitan/pss-proof)
  (`PSS.standard_P_descending`). The full lexicographic non-increase was OPEN in an earlier
  draft (now [COMB](COMB.md) §4).
- (c) ⇐: OPEN in an earlier draft (now [COMB](COMB.md) §4).
- Evidence (yaBMS): 5,292 matrices and 59,863 pairs, 0 exceptions.

**Lemma 2.1 (PROVED).** Lexicographic order on nodes = lexicographic order on the sequences
of root terms, with a proper prefix smaller. Proof: a non-first column of a one-root matrix
has $`x \ge 1`$.

**Lemma 2.2 (PROVED from S1).** Let $`\rho(t):=\mathrm{otp}\{s \in R:s \lt_p t\}`$. Then
for every node $`M=t_1 \cdots t_m`$:

- $`o(M)=\omega^{\rho(t_1)}+\cdots+\omega^{\rho(t_m)}`$;
- $`o(t)=\omega^{\rho(t)} \in P`$ for $`t \in R`$;
- $`o(\mathrm{add}(a,b))=o(a)+o(b)`$.

Proof: the order type of the non-increasing sequences over $`(R,\lt_p)`$ is the CNF.

**Corollary 2.3 (PROVED from S1).** If $`X \subseteq`$ nodes is closed under prefix sums and
root segments, then $`o[X]`$ is closed in the sense of [C01]. For $`x,y,z \in X`$:
$`o(x)+o(y)=o(z)\iff \mathrm{add}(x,y)=z`$.

**Lemma 2.4.** $`\mathrm{anchor}(N)`$ and $`\mathrm{lh}_\Phi(N)`$ are standard.

- Status ([COMB](COMB.md) §8):
  - anchor: **PROVED**;
  - $`\mathrm{lh}_\Phi(N)`$ for $`N=1`$ or $`N`$ non-epsilon: **PROVED**;
  - $`\mathrm{lh}_\Phi(N)`$ for $`N`$ epsilon: **PROVED** from [COMB](COMB.md) Lemma C (§8c,
    proved there via its Theorem SC, §8b) and T. The proof is an induction on the
    $`\mathrm{lh}`$ call tree.
  - So **Lemma 2.4 is PROVED.**

- Evidence: 125,173 distinct nodes, all standard.

---

## 3. Wilken's analysis of $`\le_1`$ that is used (CITED from [W07b])

- **Def 3.2** (for any ordinal $`\tau`$):
  - $`\alpha \ge \tau`$ is **$`\tau`$-$`\le_1`$-minimal** if every $`\beta`$ with
    $`\beta \lt_1 \alpha`$ satisfies $`\beta \le \tau`$.
  - $`\kappa^\tau`$ enumerates the $`\tau`$-$`\le_1`$-minimal ordinals, and
    $`\kappa^\tau_0=\tau`$.
  - $`\theta_\tau`$ is the supremum of the domain of $`\kappa^\tau`$.
  - $`\lambda_\tau`$ is the maximum $`\lambda \le \theta_\tau`$ with
    $`\tau \le_1 \kappa^\tau_\lambda`$.
- **Lemma 3.3.**
  - (a) $`\kappa^\tau`$ is continuous.
  - (b) $`\kappa^\tau_0=\tau`$, and
    $`\kappa^\tau_\xi=\tau+\xi=\mathrm{lh}(\kappa^\tau_\xi)`$ for
    $`\xi \in(0,\tau^L)`$. Here $`\tau^L`$ is the least element of $`L`$ above $`\tau`$.
  - (c)
    $`\kappa^\tau_{\xi+\beta}=\mathrm{lh}(\kappa^\tau_\xi)+\beta=\mathrm{lh}(\kappa^\tau_{\xi+\beta})`$
    for $`\xi \in(0,\theta_\tau)`$ and $`\beta \in(0,\mathrm{lh}(\kappa^\tau_\xi)^L)`$.
- **Lemma 3.4.**
  - (a) $`\lambda_\tau`$ is an ordinal, $`\lambda_\tau \le \theta_\tau`$,
    $`\tau \le_1 \kappa^\tau_{\lambda_\tau}`$, and
    **$`\mathrm{lh}(\tau)=\mathrm{lh}(\kappa^\tau_{\lambda_\tau})`$**.
  - (b) If $`\xi \in(0,\theta_\tau]`$ and $`\kappa^\tau_\xi \in P`$, then
    $`\kappa^\tau_\xi=\xi`$.
- **Thm 5.3** ($`\tau \in \{1\} \cup E`$; $`\alpha=\vartheta^\tau(\Delta+\eta)\in T^\tau`$;
  $`\alpha \gt \tau`$): **$`\lambda_\alpha=\lambda^\tau_\alpha`$ and
  $`\mathrm{lh}(\alpha)=\mathrm{lh}^\tau(\alpha)`$**. This uses:
  - [W07a, Def 7.5]: $`\lambda^\tau_\alpha:=\iota_{\tau,\alpha}(\Delta)+\zeta^\tau_\alpha`$
    if $`\alpha \in E`$, and $`\zeta^\tau_\alpha`$ otherwise.
  - [W07a, Def 4.11]: $`\zeta^\tau_\alpha:=\mathrm{logend}(\eta)`$ if
    $`\eta \lt \sup_{\sigma \lt \eta} \vartheta^\tau(\Delta+\sigma)`$, and 0 otherwise.
  - [W07a, Def 7.1]: $`\iota_{\tau,\alpha}:T^\tau_\alpha \to T^\alpha`$ keeps $`\xi`$ for
    $`\xi \lt \alpha`$, is additive above $`\Omega_1`$, and sends $`\vartheta_{k+1}(\eta)`$ to
    $`\vartheta_k(\iota_{\tau,\alpha}(\eta))`$, where $`\vartheta_0=\vartheta^\alpha`$.
  - [W07b, Def 4.1], the recursion for $`\mathrm{lh}^\tau(\alpha)`$ on $`h^\tau(\alpha)`$:
    - $`\mathrm{lh}^\tau(\alpha):=0`$ if $`\alpha \le \tau`$;
    - $`\mathrm{lh}^\tau(\alpha):=\alpha`$ if $`\alpha`$ is a sum;
    - for $`\alpha=\vartheta^\tau(\Delta+\eta)\gt \tau`$ put
      $`\delta:=(\lambda^\tau_\alpha)^*`$:
      - if $`\delta \le \alpha`$: $`\mathrm{lh}^\tau(\alpha):=\alpha+\lambda^\tau_\alpha`$;
      - otherwise let $`(\alpha=\delta_0,\ldots,\delta_m=\delta)`$ be the
        $`\alpha`$-localization of $`\delta`$ ([W07a, Def 4.6]) and
        $`i:=\mathrm{cr}(\alpha,\delta)`$ ([W07a, Def 7.15]: the least
        $`i \in[1,m-1]`$ with $`\lambda^\tau_{\delta_i} \ge \delta`$, or $`m`$ if there is
        none). Then
        $`\mathrm{lh}^\tau(\alpha):=\mathrm{lh}^\tau(\delta_i)+\lambda^\tau_\alpha`$ if
        $`i \lt m`$, and
        $`\mathrm{lh}^\tau(\alpha):=\mathrm{lh}^\tau(\delta)+(-\delta+\lambda^\tau_\alpha)`$
        if $`i=m`$.
- **Cor 5.9**: the greatest $`\lt_1`$-predecessor of $`\alpha`$ in $`(\tau,\alpha)`$ is
  $`\alpha_i`$ for the largest $`i \in[1,n-1]`$ with $`\lambda^\tau_{\alpha_i} \ge \alpha`$,
  where $`(\alpha_i)`$ is the $`\tau`$-localization of $`\alpha`$. If there is no such
  $`i`$, $`\alpha`$ is $`\tau`$-$`\le_1`$-minimal.

Lemma 3.3, Lemma 3.4 and Thm 2.2 are **free of notation**: they hold for all ordinals. Only
Thm 5.3 uses the $`\vartheta`$-system.

---

## 4. The reach lemma L

**Lemma L.** For every $`N \in R`$: $`\mathrm{lh}(o(N))=o(\mathrm{lh}_\Phi N)`$.

### 4.1 The reading lemma

**Lemma R (PROVED in [COMB](COMB.md) §7, by induction along fundamental sequences, using
[COMB](COMB.md) Lemmas 5 and 6).** For $`N \in R \setminus \{1\}`$:

- (i) if $`N`$ is epsilon, then $`o(N)\in E`$;
- (ii) if $`N`$ is not epsilon, then $`o(N)=\omega^{o(\log N)}`$.

Together: $`o(N)=\omega^{o(\mathcal{L} N)}`$ for all $`N \in R`$.

**Proposition 4.1 (PROVED).** Lemma R holds iff $`\mathcal{L}:R \to \text{nodes}`$ is an
order isomorphism. (Correction from [COMB](COMB.md) §9.5: first one needs
[COMB](COMB.md) Lemma 6, that $`\mathcal{L}N`$ is a node, so that $`\mathcal{L}`$ is a map
into the nodes.) Here $`\mathcal{L}(1)=()`$.

<em>Proof.</em>

- (⇐) By Lemma 2.2, $`o(N)=\omega^{\rho(N)}`$. If $`\mathcal{L}`$ is an order
  isomorphism, then
  $`\rho(N)=\mathrm{otp}\{s \lt_p N\}=\mathrm{otp}\{\text{nodes} \lt_p \mathcal{L}(N)\}=o(\mathcal{L} N)`$.
  - For epsilon $`N`$, $`\mathcal{L}(N)=(N)`$, so $`o(N)=\omega^{o(N)} \in E`$.
- (⇒) The map $`\omega^x \mapsto x`$ is an order isomorphism from $`P`$ onto
  $`\mathrm{On}`$. Also $`o{\restriction}R`$ is an order isomorphism onto
  $`P \cap \psi_0(\Omega_\omega)`$ (Lemmas 1.1 and 2.2). So
  $`\mathcal{L}=o^{-1} \circ \log_\omega \circ o`$. ∎

**Evidence.**

- A check with [poral](https://github.com/semitrivial/poral) compares $`\Phi(N)`$ with
  $`\exp(\Phi(\mathcal{L} N))`$. 74,595 root terms: 26,328 non-epsilon and 48,267 epsilon
  (with overlaps between the sets), 0 failures.
- Inline check: $`\mathcal{L}`$ is strictly increasing on 3,882 sorted roots, and every image
  is standard (yaBMS).
- **Remark.** The CNF absorption in $`\log`$ matters. For example
  $`M=(0,0)(1,1)(1,1)(1,0)(2,1)(2,1)(2,0)(3,0)`$ has the standard preimage
  $`s=(0,[(1,1),(1,1),M_0])`$, where $`\varepsilon_1`$ is absorbed by $`M_0`$. The "naive"
  preimage $`(0,[M_0])`$ is not standard.

### 4.2 The case $`N=1`$ (PROVED)

$`\mathrm{lh}_\Phi(1)=(1)`$, and 1 reaches only itself.

### 4.3 The non-epsilon case (PROVED from R)

**Lemma 4.2.** Let $`N \in R`$ be non-epsilon, $`N \ne 1`$, and put
$`\gamma:=o(\lambda(N))`$. Then

```math
\mathrm{lh}(o(N)) = o(N) + \gamma = o(\mathrm{add}((N), \lambda(N))) = o(\mathrm{lh}_\Phi N).
```

<em>Proof.</em>

1. By R(ii), $`o(N)=\omega^\zeta`$ with $`\zeta=o(\log N)`$.
2. The last term of the tuple $`\log N`$ is $`C_k`$, the last child, which has $`y=0`$. CNF
   addition never removes the last appended term. So the last CNF term of $`\zeta`$ is
   $`o(C_k)=\omega^\gamma`$, using R for $`C_k`$ read as a root term. Hence
   $`\mathrm{logend}(\zeta)=\gamma`$.
   - Correction ([COMB](COMB.md) §9.2): the fact that $`\mathrm{sh}(C_k)`$ is in $`R`$ is
     [COMB](COMB.md) Lemma 4 (Sh: the subtree of a $`y=0`$ column, shifted to the root, is
     standard), not S1(a). $`C_k`$ is a child, not a root segment. The same applies to
     $`\lambda(N)`$ and to the lo-terms of $`\log`$.
3. $`\gamma \lt \zeta \lt o(N)`$, so $`\gamma \in(0,o(N)]`$ when $`\gamma \gt 0`$.
4. **[W07b, Thm 2.2]**:
   - $`o(N)\le_1 o(N)+\gamma`$;
   - if $`\gamma+1 \le o(N)`$ (true, since $`o(N)`$ is a limit), then
     $`o(N)\not\le_1 o(N)+\gamma+1`$;
   - if $`\gamma=0`$, then $`o(N)\not\le_1 o(N)+1`$.
5. By Lemma 2.1(b, c), $`\mathrm{lh}(o(N))=o(N)+\gamma`$.
6. On the $`\Phi`$ side, $`\mathrm{lh}_\Phi(N)=\mathrm{add}((N),\lambda(N))`$. Its value is
   $`o(N)+\gamma`$ by Lemma 2.2. ∎

### 4.4 The semantic fold lemma (PROVED from [W07b] Lemmas 3.3, 3.4 and Thm 2.2)

Fix $`\alpha \in E`$ below the core. Write $`K(\xi):=\mathrm{lh}(\kappa^\alpha_\xi)`$ for
$`0 \lt \xi \le \lambda_\alpha`$, and $`\mathrm{lead}(\beta)`$ for the first term of the ANF
of $`\beta`$.

**Lemma F.**

- (F1) $`\alpha \le \lambda_\alpha`$ and $`K(\alpha)=\alpha \cdot 2`$.
- (F2) Let $`0 \lt \xi \lt \lambda_\alpha`$ and $`Y \in P`$ with
  $`\xi+Y \le \lambda_\alpha`$.
  - (a) If $`Y \le \mathrm{lead}(K(\xi))`$, then $`K(\xi+Y)=K(\xi)+Y`$.
  - (b) If $`Y \gt \mathrm{lead}(K(\xi))`$ and $`Y`$ is $`\alpha`$-$`\le_1`$-minimal, then
    $`\xi+Y=Y`$ and $`K(\xi+Y)=\mathrm{lh}(Y)`$.
- (F3) $`\mathrm{lh}(\alpha)=K(\lambda_\alpha)`$.

<em>Proof.</em>

- (F1) $`\alpha \in E`$, so $`\alpha \le_1 \alpha \cdot 2`$ (Thm 2.2). By Lemma 3.3(b),
  $`\kappa^\alpha_\alpha=\alpha+\alpha`$, since $`\alpha \lt \alpha^L`$, and
  $`\mathrm{lh}(\alpha \cdot 2)=\alpha \cdot 2`$. So $`\alpha \le_1 \kappa^\alpha_\alpha`$
  and $`\alpha \le \lambda_\alpha`$.
- (F2a) $`Y \le \mathrm{lead}(K(\xi))`$ implies
  $`Y \lt K(\xi)\cdot \omega \le K(\xi)^L`$. Also
  $`\xi \lt \lambda_\alpha \le \theta_\alpha`$. Lemma 3.3(c) with $`\beta=Y`$ gives the
  claim.
- (F2b)
  - $`\kappa^\alpha`$ is strictly increasing, so
    $`\xi \le \kappa^\alpha_\xi \le K(\xi)\lt \mathrm{lead}(K(\xi))\cdot \omega \le Y`$.
    Since $`Y \in P`$, $`\xi+Y=Y`$.
  - $`Y`$ is $`\alpha`$-$`\le_1`$-minimal, so $`Y=\kappa^\alpha_\zeta`$ for some
    $`\zeta`$. Since $`\kappa^\alpha_\zeta \in P`$, Lemma 3.4(b) gives $`\zeta=Y`$.
  - Hence $`K(Y)=\mathrm{lh}(Y)`$.
- (F3) This is Lemma 3.4(a). ∎

### 4.5 The epsilon case

Let $`N`$ be epsilon, $`\alpha=o(N)`$, $`A=(C_1,\ldots,C_k)`$ and $`W=C_k`$.

- By [COMB](COMB.md) Lemma 1 (T3, T4): all root children of an epsilon $`N`$ have
  $`y=1`$ (so $`y(W)=1`$), and the children of $`W`$ with $`y=2`$ (the $`D`$'s) come
  before the $`E`$'s.

Let $`D_1,\ldots,D_p`$ be the children of $`W`$ with $`y \ge 2`$, and
$`E_1,\ldots,E_q`$ those with $`y \le 1`$. The fold inputs are, in order:

```math
\begin{aligned}
Y_i &:= (0,\ A + \mathrm{Coll}_A(D_1) + \cdots + \mathrm{Coll}_A(D_i)) && (i = 1, \ldots, p), \cr
Y_{p+j} &:= \mathrm{Coll}_A(E_j) && (j = 1, \ldots, q).
\end{aligned}
```

Then $`\mathrm{lh}_\Phi(N)=S_n`$, where $`S_0=(N,N)`$ and
$`S_j=S_{j-1} \oplus Y_j`$. Call step $`j`$ a **jump** if $`Y_j \gt S_{j-1,1}`$, the
leading term of $`S_{j-1}`$.

**E1 (PROVED given TR; [§12.5](PROOF-2.md)).**
$`\lambda_\alpha=\alpha+o(Y_1)+\cdots+o(Y_n)`$ (ordinal sum).

**E2 (PROVED given TR; [§14.3](PROOF-3.md), inside the induction of Prop 4.3, see below).** For every jump
step $`j`$, $`o(Y_j)`$ is $`\alpha`$-$`\le_1`$-minimal.

**T (PROVED in [COMB](COMB.md) §8).** The recursion of $`\mathrm{lh}_\Phi`$ terminates.

- The depth of nested calls is $`\lt \mathrm{height}(W_N)`$.
- The proof uses a provenance invariant: every nested epsilon call $`Z`$ carries a proper
  subterm $`d_Z`$ of $`W_N`$ with $`W_Z=\Phi_Z(d_Z)`$. The measure must follow this
  provenance, because $`W_Z`$ itself can grow.

**Proposition 4.3 (PROVED from Lemma F).** If E1, E2 and T hold, then Lemma L holds for all
epsilon $`N`$.

<em>Proof.</em> By induction on the recursion tree of $`\mathrm{lh}_\Phi`$, which is finite by T.
Put $`\xi_0:=\alpha`$ and $`\xi_j:=\xi_{j-1}+o(Y_j)`$. The claim is
$`K(\xi_j)=o(S_j)`$ for all $`j`$.

- **$`j=0`$:** F1.
- **Step, no jump:** $`o(Y_j)\le \mathrm{lead}(o(S_{j-1}))`$ (Lemma 2.2), so by F2(a),
  $`K(\xi_j)=o(S_{j-1})+o(Y_j)=o(S_{j-1}+(Y_j))`$.
- **Step, jump:** by E2 and F2(b), $`K(\xi_j)=\mathrm{lh}(o(Y_j))`$. By the induction
  hypothesis applied to $`Y_j`$ (a smaller call), this is
  $`o(\mathrm{lh}_\Phi Y_j)=o(S_j)`$.
- **Conclusion:** by E1, $`\xi_n=\lambda_\alpha`$, and by F3,
  $`\mathrm{lh}(\alpha)=K(\lambda_\alpha)=o(S_n)=o(\mathrm{lh}_\Phi N)`$. ∎

**The order of the induction (M7).** E2 is not a separate hypothesis. It is proved inside
this induction. The full scheme:

- **Outer induction** on the $`\mathrm{lh}_\Phi`$ call tree of $`N`$, which is finite by
  [COMB](COMB.md) T. Its hypothesis: L holds for every call below $`N`$, in particular for
  every jump input $`Y_j`$.
- **Inner induction** on $`j=0,1,\ldots,n`$, proving together:
  - $`(P_j)`$ $`K(\xi_j)=o(S_j)`$, and $`\xi_j \le \lambda_\alpha`$;
  - $`(\mathrm{E2}_j)`$ if step $`j`$ is a jump, then $`o(Y_j)`$ is
    $`\alpha`$-$`\le_1`$-minimal.
- **Step $`j \ge 1`$.**
  1. First prove $`(\mathrm{E2}_j)`$. Its proof ([§14.3](PROOF-3.md): PL, then the Cor 5.9 argument)
     uses:
     - $`(P_{j-1})`$, in the form $`K:=K(\xi_{j-1})=o(S_{j-1})`$;
     - the syntactic facts about the earlier inputs $`Y_1,\ldots,Y_{j-1}`$.

     It does not use $`(P_j)`$.
  2. Then prove $`(P_j)`$ as in the proof above:
     - F2(a) for a non-jump;
     - F2(b) with $`(\mathrm{E2}_j)`$ and the outer hypothesis $`L(Y_j)`$ for a jump.
  3. $`\xi_j \le \lambda_\alpha`$ holds because $`\xi_j \le \xi_n=\lambda_\alpha`$ (E1).
- **Why the pieces fit.**
  - E1 is a statement about the inputs alone. Its proof ([§12.5](PROOF-2.md), from CI and TR) uses neither
    $`(P_j)`$ nor $`(\mathrm{E2}_j)`$, so it can be used at every $`j`$.
  - Hence there is no circularity.

**E1 checked by hand against [W07a, Def 7.5] and [W07b, Def 4.1]** ($`\tau=1`$). The
matrices and $`\vartheta`$-forms are Wilken's own examples ([W21] §1, §2.2).

| $`\alpha`$ | matrix $`N`$ | $`\vartheta`$-form | $`\lambda_\alpha=\iota(\Delta)+\zeta_\alpha`$ | $`\Phi`$ fold inputs $`Y`$ | $`\alpha+\Sigma Y`$ | $`\mathrm{lh}`$ (Wilken = $`\Phi`$) |
|---|---|---|---|---|---|---|
| $`\varepsilon_0`$ | $`(0,0)(1,1)`$ | $`\vartheta(\Omega)`$ | $`\alpha`$ | — | $`\alpha`$ | $`\alpha \cdot 2`$ |
| $`\varepsilon_1`$ | $`(0,0)(1,1)(1,1)`$ | $`\vartheta(\Omega+1)`$ | $`\alpha`$ ($`\zeta=\mathrm{logend}\ 1=0`$) | — | $`\alpha`$ | $`\alpha \cdot 2`$ |
| $`\varepsilon_\omega`$ | $`(0,0)(1,1)(2,0)`$ | $`\vartheta(\Omega+\omega)`$ | $`\alpha+1`$ | $`\mathrm{Coll}(2,0)=1`$ | $`\alpha+1`$ | $`\alpha \cdot 2+1`$ |
| $`\varphi(2,0)`$ | $`(0,0)(1,1)(2,1)`$ | $`\vartheta(\Omega+\Omega)`$ | $`\alpha \cdot 2`$ | $`\mathrm{Coll}(2,1)=N`$ | $`\alpha \cdot 2`$ | $`\alpha \cdot 3`$ |
| $`\varepsilon_{\varepsilon_0}`$ | $`(0,0)(1,1)(2,0)(3,1)`$ | $`\vartheta(\Omega+\varepsilon_0)`$ | $`\alpha+\varepsilon_0`$ | $`\mathrm{Coll}((2,0)(3,1))=\varepsilon_0`$ | $`\alpha+\varepsilon_0`$ | $`\alpha \cdot 2+\varepsilon_0`$ |
| $`\Gamma_0`$ | $`(0,0)(1,1)(2,1)(3,1)`$ | $`\vartheta(\vartheta_1(\vartheta_1(0)))`$ | $`\iota(\Delta)=\vartheta^\alpha(\alpha)=\omega^{\alpha \cdot 2}`$; $`\delta=\lambda \gt \alpha`$, localization $`(\alpha,\delta)`$, $`\mathrm{cr}=m=1`$ | $`Y=n1=(0,0)(1,1)(2,1)(3,1)(1,0)(2,1)(3,1)(4,1)=\omega^{\alpha \cdot 2}`$, **a jump** | $`\omega^{\alpha \cdot 2}`$ | $`\mathrm{lh}(\delta)+0=\omega^{\alpha \cdot 2}+\alpha`$ |
| BHO | $`(0,0)(1,1)(2,2)`$ | $`\vartheta(\vartheta_1(\vartheta_2(0)))`$ | $`\iota(\Delta)=\vartheta^\alpha(\Omega)=\varepsilon_{\alpha+1}`$; $`\mathrm{cr}=m=1`$ | $`Y=(0,0)(1,1)(2,2)(1,1)=\varepsilon_{\alpha+1}`$, **a jump** | $`\varepsilon_{\alpha+1}`$ | $`\mathrm{lh}(\varepsilon_{\alpha+1})=\varepsilon_{\alpha+1} \cdot 2`$ |

All seven agree with the output of [phi.py](../por/phi.py) ([POR.md](../POR.md) §4, and
earlier runs).

**The dictionary the tables suggest** (this is what a proof of E1 must make precise):

- $`S_0=(N,N)`$ consumes the index $`\alpha=\iota_{1,\alpha}(\vartheta_1(0))`$, the
  leading $`\Omega`$ of $`\Delta`$.
- $`\mathrm{Coll}_A`$ on a $`y=0`$ subtree is the identity; these are the parameters below
  $`\alpha`$.
- $`\mathrm{Coll}_A`$ on $`y \ge 2`$ lowers $`y`$ by one:
  $`\vartheta_{k+1} \mapsto \vartheta_k`$ in $`\iota_{\tau,\alpha}`$.
- $`\mathrm{Coll}_A`$ on $`y=1`$ gives "$`N`$ with the children appended":
  $`\vartheta_1 \mapsto \vartheta^\alpha`$, written back in $`T^1`$ by the translation
  $`t^\alpha_\tau`$ ([W07a, Def 6.2, Lemma 6.3]).
- The $`D`$-prefixes $`(0,A+\mathrm{Coll}(D_1..D_i))`$ run through the
  $`\vartheta_1`$-summands of $`\Delta`$.
- The $`E_j`$ run through the rest of $`\Delta`$ and through $`\zeta_\alpha`$.
- The jumps are the cases $`\delta \gt \alpha`$ of Def 4.1, with the $`\alpha`$-localization
  and $`\mathrm{cr}`$.

**What a proof of E1 and E2 needs.** An explicit translation
$`\mathcal{T}:\mathrm{Std} \to T^1`$ with $`\mathrm{val} \circ \mathcal{T}=o`$, commuting
with $`\mathrm{Coll}_A \leftrightarrow t^\alpha_\tau \circ \iota_{1,\alpha}`$. See §4.6.

### 4.6 The translation to $`\vartheta`$-terms: status after [WW11]

**What [WW11] provides (CITED).** [WW11] = Weiermann–Wilken, MLQ 57 (2011) 116–132.

- **Def 2.1:** simultaneously defined $`\bar\vartheta_i`$ (Buchholz-style Skolem hulls
  $`\bar C_i(\alpha,\beta)`$). Here $`\bar\vartheta_i(\alpha)`$ is the least
  $`\xi \lt \Omega_{i+1}`$ with $`\alpha \in \bar C_i(\alpha,\xi)`$ and
  $`\bar C_i(\alpha,\xi)\cap \Omega_{i+1} \subseteq \xi`$.
- **Lemma 2.12:** explicit values.
  - (b) For $`\alpha \lt \Omega_{m+1}`$: $`\bar\vartheta_m(\alpha)=\omega^{\alpha+1}`$ if
    $`\alpha=\alpha'+n`$ with $`\alpha' \in E_{\gt\Omega_m}`$, and
    $`\bar\vartheta_m(\alpha)=\omega^{-1+\Omega_m+\alpha}`$ otherwise.
  - (d) The values $`\bar\vartheta_m(\Omega_{m+1}+\alpha)`$ are epsilon numbers.
- **Lemma 3.1:** $`\bar\vartheta_m=\vartheta_m`$ on $`\varepsilon_{\Omega_{m+1}+1}`$.
- **Def 3.2 ($`\mathrm{it}_m`$), Def 3.3 ($`\mathrm{rt}_m`$), Main Lemma 3.5, Lemma 3.6,
  Cor 3.7:** $`\mathrm{it}_m`$ and $`\mathrm{rt}_m`$ are mutually inverse and strictly
  increasing, and **$`\vartheta_m=\bar\vartheta_m \circ \mathrm{it}_m`$** and
  **$`\bar\vartheta_m=\vartheta_m \circ \mathrm{rt}_m`$**.
- **Thm 3.8:** an elementary recursive order isomorphism $`\bar T_m \cong T_m`$.
- **Def 3.9:** $`f^\tau:T^\tau \to \bar T^\tau`$, with
  $`f^\tau(\vartheta_m(\xi))=\bar\vartheta_m(\mathrm{it}_m(\xi))`$.
  - By Cor 3.7(f), $`f^\tau`$ fixes every value below $`\Omega_1`$. Only the argument terms
    change.
  - Hence [W07b]'s results on $`\mathrm{lh}`$, which are about ordinals, may be read in
    either system.
- **Def 5.4:** $`\iota_{\tau,\alpha}`$ on $`\bar T`$.
- **§5:** Sections 4–8 of [W07a] (localization, base transformation, translation,
  $`\lambda`$, cofinality) "carry over" to $`\bar T^\tau`$.

**What does not exist in the literature.** A translation between Buchholz's $`\psi_\nu`$
([B86], the target of `pairTerm`) and $`\bar\vartheta`$ or $`\vartheta`$. [WW11] p.117 says
so explicitly:

> "A precise translation between ϑ, ϑ̄ and … Buchholz' ψ-functions, see [4], … seems
> rewarding and we leave this for future research. (Partial results based on
> embeddings have already been established.)"

So step 2 of the route in §4.5 (Buchholz $`\psi \to \bar\vartheta`$) is itself new research.

**Lemma TR (an earlier formulation; superseded: $`\mathcal{T}`$ is defined in [§12.1](PROOF-2.md) and TR is
proved in [TR](TR.md)).** There is a translation $`\mathcal{T}:R \to \bar T^1`$
(equivalently, by $`f^\tau`$, into $`T^1`$) such that:

- $`\mathrm{val}(\mathcal{T} N)=o(N)`$;
- for epsilon $`N`$ and $`Y_j`$ a fold input, $`\mathcal{T}(Y_j)`$ and the ANF terms of
  $`\lambda_{o(N)}=\iota(\Delta)+\zeta`$ correspond as in the dictionary of §4.5.

Given TR, E1 becomes a syntactic identity in $`T^1`$ that can be checked by the recursions
of [W07a] Def 7.1 and Def 7.5.

**Why the translation is not a direct recursion.**

- On the Buchholz side, the collapsed arguments are $`\Omega`$-<em>exponential</em>. On Wilken's
  side they are $`\Omega`$-<em>linear</em>, because the $`\vartheta`$ are free of fixed points
  ([WW11] Lemma 2.12).
- Values, from the Lean `pairTerm` (checked with
  [pss-proof](https://github.com/koteitan/pss-proof)'s `trans_model`) and from [W21] §1:

  | ordinal | Buchholz form | Wilken form |
  |---|---|---|
  | $`\varepsilon_0`$ | $`\psi_0(\Omega)`$ | $`\vartheta(\Omega)`$ |
  | $`\varepsilon_1`$ | $`\psi_0(\Omega \cdot 2)`$ | $`\vartheta(\Omega+1)`$ |
  | $`\varepsilon_\omega`$ | $`\psi_0(\Omega \cdot \omega)`$ | $`\vartheta(\Omega+\omega)`$ |
  | $`\varphi(2,0)`$ | $`\psi_0(\Omega^2)`$ | $`\vartheta(\Omega \cdot 2)`$ |
  | $`\Gamma_0`$ | $`\psi_0(\Omega^\Omega)`$ | $`\vartheta(\vartheta_1(\vartheta_1(0)))=\vartheta(\Omega^2)`$ |
  | Bachmann–Howard (BHO) | $`\psi_0(\Omega_2)`$ | $`\vartheta(\vartheta_1(\vartheta_2(0)))`$ |

- So the translation takes a logarithm to base $`\Omega`$ at every collapsing level.
- At level 1, below $`\varepsilon_{\Omega+1}`$, the values agree:
  $`\psi_1(e)=\omega^{\Omega+e}=\vartheta_1(e)`$, by [WW11] Lemma 2.12(b) with $`m=1`$.
- A proof of TR would go by structural induction, but with a level-shifting logarithm. This
  is the analogue of [WW11] Def 3.2, one level of simultaneous-versus-stepwise shifted. It is
  not done here.

### 4.7 E2 as a combinatorial statement

**Prop 4.4 (PROVED from Lemma L on the nodes in $`(N,Y)`$, Lemma 1.1, Cor 1.2 and
Lemma 3.1(c)).** Let $`Y`$ be a jump input of the fold for epsilon $`N`$. Then $`E2(Y)`$
holds iff:

```math
\mathrm{C2}(N, Y):\ \text{there is no one-root node } z \text{ with } N \lt_p z \lt_p Y \text{ and } Y \le_p \mathrm{lh}_\Phi(z).
```

<em>Proof.</em>

- (⇐) Let $`\beta \in(o(N),o(Y))`$ with $`\beta \lt_1 o(Y)`$.
  - $`\beta=o(z)`$ for a node $`z`$ with $`N \lt_p z \lt_p Y`$ (Lemma 1.1).
  - $`\beta \in P`$ (Lemma 3.1(c)), so $`z`$ has one root (Lemma 2.2).
  - By L for $`z`$ and Cor 1.2, $`o(Y)\le \mathrm{lh}(\beta)=o(\mathrm{lh}_\Phi z)`$. So
    $`Y \le_p \mathrm{lh}_\Phi(z)`$, against C2.
- (⇒) Such a $`z`$ gives $`o(z)\le_1 o(Y)`$ (L for $`z`$ and Cor 1.2) with
  $`o(z)\gt o(N)`$. So $`o(Y)`$ is not $`o(N)`$-$`\le_1`$-minimal. ∎

**Remark.** This does not break the circularity by itself. Prop 4.3 needs L for the jumps
$`Y`$ (above $`N`$), and Prop 4.4 needs L for nodes between $`N`$ and $`Y`$. [W07b] Thm 5.3
breaks the same circle by main induction on the height $`\mathrm{ht}^\tau`$ and side
induction on $`\alpha`$. It uses that the nodes strictly between $`\alpha_k`$ and
$`\alpha_{k+1}`$ have smaller relative height ([W07b] proof of (1)).

A PSS proof needs the corresponding measure (a relative maximum of $`y`$). That is the
measure of the termination statement T, which is outside this note.

(Superseded note: E1 is now PROVED given TR, [§12.5](PROOF-2.md).)

**Evidence for Lemma L and E2.**

- Test M: 74,595 root terms, reach maximal in every case.
- Test E (§6): 1,244,496 checks.
- E2 checked inside $`\Phi`$: 40,258 jump inputs $`Y`$. There is no generated root
  $`\beta`$ with $`N \lt \beta \lt Y`$ and $`\mathrm{lh}_\Phi(\beta)\ge Y`$ (17,798
  $`\beta`$ checked).
- **Test J** (semantic, with [poral](https://github.com/semitrivial/poral) as oracle), for
  every jump input $`Y`$ of every epsilon root $`N`$ in the generated sets:
  - (i) C2 on all nodes of the closure of $`\{N,Y\}`$;
  - (ii) a fresh indecomposable $`b`$ is inserted into every gap between $`N`$ and $`Y`$,
    with $`b \le_1 Y`$ and the $`\le_1`$-forest closed under transitivity. It counts as a
    violation if poral still realizes both $`N`$ and $`Y`$ at their $`\Phi`$-values.
  - Result: 40,350 jumps, 89,710 gap tests, **0 violations**. 808 poral crashes (all in gap
    tests), 0 rejections.
  - Controls: $`Y=\omega^{\Gamma_0 \cdot 2}`$ relative to $`N=1`$ or $`N=\omega`$ is
    caught by C2, since $`\Gamma_0`$ lies between them. The true jump ($`N=\Gamma_0`$) and
    $`\zeta_0`$ relative to 1 pass.
  - The gap part could not be validated by a positive control: in every candidate tried, the
    $`\lt_1`$-predecessor already enters the closure through anchor or $`\mathrm{lh}`$.

---

## 5. The embedding lemma

$`\Phi(M)`$ is the pattern with:

- universe $`V_M`$, the closure of $`\{(),(1),M\}`$ under prefix sums, root segments,
  anchor and $`\mathrm{lh}_\Phi`$;
- the order $`\lt_p`$ and the constant $`0=()`$;
- the addition graph $`\mathrm{add}`$;
- $`x \le_1 z`$ iff $`x=z`$, or ($`x`$ has one term and
  $`x \le_p z \le_p \mathrm{lh}_\Phi x`$);
- the point $`M`$.

**Finiteness.** $`V_M`$ is finite, and $`o[V_M]=P_1(o(M))`$ (Thm VF and Cor VF, [§15.1](PROOF-4.md)).
This is needed for $`\Phi(M)`$ to be a pattern ([C01] Def 4.2). It was the referee's
BLOCKING item B1.

**Lemma 5.1 (PROVED from S1, 2.4, L, and Thm VF for finiteness).** $`o{\restriction}V_M`$ is
an isomorphism of $`\Phi(M)`$ onto a finite closed substructure of $`R_1`$.

<em>Proof.</em>

- Order: Lemma 1.1.
- 0, $`+`$ and closedness: Cor 2.3.
- $`\le_1`$:
  - a sum reaches only itself ([W07b] §2, Thm 2.2 remark);
  - 0 and 1 reach only themselves;
  - a one-term $`x`$: Cor 1.2 and Lemma L. ∎

**Cor 5.2 (PROVED from 5.1, C1).** $`\iota(\Phi(M))\le o(M)`$: $`o[V_M]`$ is a cover of
$`\Phi(M)`$, and C1(4) applies.

---

## 6. Lemma 6.1, and Route B (Route B is not needed)

Write $`f(M):=\iota(\Phi(M))`$.

**Lemma 6.1 (Sandwich; PROVED from C1).** Let $`X`$ be a finite closed set, let
$`Z \subseteq X`$ be isominimal, and let $`\alpha \in Z`$. Let $`h:X \to X^*`$ be the
isomorphism onto the isominimal copy $`X^*`$ of $`X`$. Then $`h(\alpha)=\alpha`$.

<em>Proof (written out for referee item M2).</em>

1. **$`h`$ lowers every point.** $`X`$ is a covered pattern: the identity is a covering. By
   C1 there are $`X^* \cong X`$, and $`h:X \to X^*`$, with $`X^* \le_{\mathrm{pw}} X`$
   (C1(4) with $`Q=X`$). $`h`$ is order preserving between finite sets, and
   $`X^* \le_{\mathrm{pw}} X`$ compares the $`i`$-th elements. So $`h(q)\le q`$ for every
   $`q \in X`$.
2. **$`h`$ maps $`Z`$ onto a copy of $`Z`$ below it.**
   - $`h`$ is an isomorphism between substructures of $`R_1`$ ($`0,+,\le,\le_1`$). So
     $`h{\restriction}Z`$ is an isomorphism of $`Z`$ onto $`h[Z]`$, as substructures of
     $`R_1`$.
   - The $`i`$-th element of $`h[Z]`$ is $`h`$(the $`i`$-th element of $`Z`$), which is
     $`\le`$ that element. So $`h[Z]\le_{\mathrm{pw}} Z`$.
3. **Minimality of $`Z`$.**
   - [C01] p.25: $`Z`$ isominimal means $`Z=C`$ for every $`C \cong Z`$ with
     $`C \le_{\mathrm{pw}} Z`$. So $`h[Z]=Z`$.
   - [CW12]'s isominimality (closed, and $`\le_{\mathrm{pw}}`$-minimal among the isomorphic
     finite sets) implies [C01]'s, so either reading applies. [CW12] Cor 6.3(1) gives the
     [CW12] form.
4. **Conclusion.** $`h{\restriction}Z`$ is an order isomorphism of the finite set $`Z`$ onto
   itself, hence the identity. So $`h(\alpha)=\alpha`$. ∎

**Route B (not needed).** Thm 6.3 and Lemma 6.4 below were the first route to the Main
Theorem. Route A ([§11.2](PROOF-2.md), Thm 11.1) replaces them. Lemma 6.4 for epsilon $`N`$ stays
unproved, and nothing in the Main Theorem uses it. The text is kept for the record.

**Theorem 6.3 (PROVED from S1, 2.4, L, C1, and Lemma 6.4 below).** $`f(M)=o(M)`$ for every
$`M \in \mathrm{Std}`$.

<em>Proof.</em> By induction on $`M`$ along the well-order $`\lt_p`$ (`isWellOrder_pairLt`).

1. **Setup.** Let $`P=\Phi(M)`$. By Lemma 5.1, $`Q:=o[V_M]`$ is a cover of $`P`$. By C1
   there is an isomorphism $`h:Q \to P^*`$ with $`P^* \le_{\mathrm{pw}} Q`$. Since $`h`$ is
   order preserving, $`h(q)\le q`$ for all $`q \in Q`$.
2. **Every node below $`M`$ is fixed.** Let $`x \in V_M \cap \mathrm{Std}`$ with
   $`x \lt_p M`$.
   - $`V_x \subseteq V_M`$, because $`V_M`$ is closed under the operations that generate
     $`V_x`$.
   - $`h{\restriction}o[V_x]`$ is an isomorphism onto a substructure of $`R_1`$. By
     Lemma 5.1 it is a cover of $`\Phi(x)`$.
   - By C1(4) applied to $`\Phi(x)`$, $`\Phi(x)^* \le_{\mathrm{pw}} h[o[V_x]]`$. At the
     position of $`x`$ this reads $`f(x)\le h(o(x))`$.
   - By the induction hypothesis $`f(x)=o(x)`$. So $`h(o(x))\ge o(x)`$, and hence
     $`h(o(x))=o(x)`$.
   - Also $`h(0)=0`$. So $`h`$ fixes $`o(x)`$ for every node $`x \in V_M`$ with
     $`x \lt_p M`$.
3. **$`M`$ with several terms.** If $`M=(t_1,\ldots,t_m)`$ with $`m \ge 2`$, then
   $`\mathrm{pre}:=(t_1,\ldots,t_{m-1})`$ and $`(t_m)`$ are in $`V_M`$, and both are
   $`\lt_p M`$. They are fixed, and $`o(M)=o(\mathrm{pre})+o(t_m)`$ is a $`+`$-relation
   inside $`Q`$. So $`h(o(M))=o(M)`$.
4. **$`M`$ with one term.** Lemma 6.4 below gives $`h(o(M))=o(M)`$.
5. **Conclusion.** $`f(M)=h(o(M))=o(M)`$. ∎

**Lemma 6.4 (Minimality).** Let $`N \in R`$, $`Q=o[V_N]`$, and let $`h`$ be an isomorphism
of $`Q`$ onto a substructure of $`R_1`$ with:

- $`h(q)\le q`$ for all $`q \in Q`$;
- $`h(q)=q`$ for all $`q \in Q`$ with $`q \lt o(N)`$.

Then $`h(o(N))=o(N)`$.

**Case $`N=1`$ (PROVED):** 1 is the only element between 0 and 1.

**Case $`N`$ non-epsilon (PROVED from R, 2.4 and [W07b, Thm 2.2]).**

<em>Proof.</em>

1. **Where $`h(o(N))`$ can lie.** Put $`\mu:=h(o(N))`$.
   - $`o(N)`$ is indecomposable in $`Q`$.
   - $`h[Q]`$ is closed, since $`P^*`$ is closed by C1(2).
   - So $`\mu`$ is indecomposable, that is $`\mu \in P`$, and $`\mu \le o(N)`$.
2. **Writing $`o(N)`$.**
   - Let $`a:=\mathrm{anchor}(N)`$ if $`k \ge 2`$, with $`o(a)=\omega^\xi`$,
     $`\xi=o(\mathcal{L} a)`$ by R.
   - Let $`a:=1`$ if $`k=1`$, with $`\xi=0`$.
   - In both cases $`o(a)`$ is fixed by $`h`$: $`a \in V_N`$, $`a \lt_p N`$, and
     $`1 \in V_N`$.
   - Then $`o(N)=\omega^{\xi+\omega^\gamma}`$, with $`\gamma=o(\lambda(N))`$.
   - This holds because $`\log N=\mathcal{L}(a)+C_k`$ as a CNF sum:
     - if $`C_{k-1} \in \mathrm{hi}`$, then $`a`$ is epsilon and $`\log N=(a)+C_k`$;
     - otherwise $`\log N=\log(a)+C_k`$.
     - Then use R for $`N`$ and for $`C_k`$.
3. **The reach of $`\mu`$.**
   - $`L:=\mathrm{lh}_\Phi(N)=(N,\lambda_1,\ldots,\lambda_r)`$ is in $`V_N`$. Its
     prefix sums and the root segments $`\lambda_i`$ are in $`V_N`$, and
     $`\lambda_i \lt_p N`$, so the $`\lambda_i`$ are fixed.
   - Since $`h`$ keeps the $`+`$-relations along the prefix sums,
     $`h(o(L))=\mu+\gamma`$.
   - Since $`N \le_1 L`$ in $`\Phi(N)`$ and $`h`$ keeps $`\le_1`$ (it is an isomorphism),
     $`\mu \le_1 \mu+\gamma`$.
4. **The case $`\gamma=0`$.** There is no additive principal number in
   $`(\omega^\xi,\omega^{\xi+1})`$. Since $`o(a)=\omega^\xi \lt \mu \le o(N)=\omega^{\xi+1}`$,
   we get $`\mu=o(N)`$.
5. **The case $`\gamma \gt 0`$.**
   - $`\gamma \lt \mu`$, because each $`\lambda_i \lt \mu`$ and $`\mu \in P`$.
   - By Thm 2.2, $`\mu=\omega^{\mu'}`$ with $`\mathrm{logend}(\mu')\ge \gamma`$.
   - $`\omega^\xi \lt \mu \le \omega^{\xi+\omega^\gamma}`$, so
     $`\xi \lt \mu' \le \xi+\omega^\gamma`$.
   - If $`\mu' \lt \xi+\omega^\gamma`$, then $`\mu'=\xi+\rho`$ with
     $`0 \lt \rho \lt \omega^\gamma`$, and
     $`\mathrm{logend}(\mu')=\mathrm{logend}(\rho)\lt \gamma`$. This is a contradiction.
   - Hence $`\mu'=\xi+\omega^\gamma`$ and $`\mu=o(N)`$. ∎

**Case $`N`$ epsilon, first step (PROVED from L via Lemma 5.1, and Thm 2.2).**
$`\mu:=h(o(N))`$ lies in $`E`$, and $`\max(Q \cap o(N))\lt \mu \le o(N)`$.

<em>Proof.</em>

1. **$`\mu \in P`$ and the lower bound.** As in the non-epsilon case, $`\mu \in P`$. Also
   $`\mu \gt h(q)=q`$ for every $`q \in Q`$ below $`o(N)`$.
2. **The first root segment of $`L=\mathrm{lh}_\Phi(N)`$.** It is in $`V_N`$.
   - If the fold has no jump, $`L=(N,N,\ldots)`$ and the prefix $`(N,N)\in V_N`$. So
     $`h(o(N)\cdot 2)=\mu \cdot 2 \le h(o(L))`$.
   - If there is a jump, the first root segment is the last jump input $`Y`$, with
     $`Y \gt_p N`$. Then $`h(o(Y))\in P`$ and $`h(o(Y))\gt \mu`$, so
     $`h(o(Y))\ge \mu \cdot \omega \gt \mu \cdot 2`$, and $`h(o(L))\ge h(o(Y))`$.
3. **Conclusion.** $`N \le_1 L`$ in $`\Phi(N)`$ gives $`\mu \le_1 h(o(L))`$. By [W07b]
   Lemma 2.1(b), $`\mu \le_1 \mu \cdot 2`$. By Thm 2.2 ($`\xi=\mu`$), $`\mu \in E`$. ∎

**Case $`N=\Gamma_0=(0,0)(1,1)(2,1)(3,1)`$ (PROVED from L, [W07b] Thm 2.2, Thm 5.3 and
Def 4.1, [W07a] Lemma 3.30, Lemma 4.2, Def 7.1 and Def 7.5).**

Setup:

- $`o(N)=\Gamma_0`$ ($`\mathrm{pairTerm}=D_0 D_1 D_1 D_1 0=\psi_0(\Omega^\Omega)=\Gamma_0`$).
- $`V_N=\{0,1,\Gamma_0,n1,n1+\Gamma_0\}`$, where
  $`n1=(0,0)(1,1)(2,1)(3,1)(1,0)(2,1)(3,1)(4,1)`$ and
  $`o(n1)=\omega^{\Gamma_0 \cdot 2}`$. In $`\Phi(N)`$: $`\Gamma_0 \le_1 n1+\Gamma_0`$ and
  $`n1 \le_1 n1+\Gamma_0`$.
- The first step gives $`\mu \in E \cap(1,\Gamma_0]`$.

<em>Proof.</em>

1. **A lower bound for $`\nu:=h(o(n1))`$.**
   - $`\nu \in P`$, $`\nu \gt \mu`$, and $`\nu \le_1 \nu+\mu`$.
   - By Thm 2.2, $`\nu=\omega^{\nu'}`$ with $`\mathrm{logend}(\nu')\ge \mu`$.
   - Since $`\nu' \gt \mu=\omega^\mu`$, this forces $`\nu' \ge \mu \cdot 2`$. So
     $`\nu \ge \omega^{\mu \cdot 2}`$.
2. **What $`\mu`$ must reach.** $`\mu \le_1 \nu+\mu`$, so
   $`\mathrm{lh}(\mu)\ge \nu+\mu \gt \omega^{\mu \cdot 2}`$.
3. **Every epsilon $`\mu \lt \Gamma_0`$ has $`\mathrm{lh}(\mu)\lt \omega^{\mu \cdot 2}`$.**
   Write $`\mu=\vartheta(\Delta+\eta)`$ with $`\Delta \gt 0`$ ([W07a] Lemma 4.3).
   - **Bounding $`\Delta`$.** By Lemma 3.30,
     $`\mu \lt \vartheta(\vartheta_1(\vartheta_1(0)))`$ forces
     $`\Delta+\eta \lt \vartheta_1(\vartheta_1(0))`$. So
     $`\Delta=\vartheta_1(\zeta_1)+\cdots+\vartheta_1(\zeta_k)`$ with every
     $`\zeta_i \lt \Omega`$. Also $`\zeta_i,\eta \lt \mu`$, because the
     $`\vartheta_0`$-parts are $`\lt \mu`$ (Lemma 3.30) and $`\mu \in P`$.
   - **Bounding $`\lambda_\mu`$.**
     $`\lambda_\mu=\iota(\Delta)+\zeta_\mu=\Sigma\, \vartheta^\mu(\zeta_i)+\zeta_\mu`$
     (Def 7.1, Def 7.5). Here $`\vartheta^\mu(0)=\mu`$ and
     $`\vartheta^\mu(1+\beta)=\bar\omega^{\mu+\beta}=\omega^{\mu+1+\beta} \lt \omega^{\mu \cdot 2}`$
     (Lemma 4.2, relativised to $`\mu`$), and $`\zeta_\mu \le \eta \lt \mu`$. So
     $`\lambda_\mu \lt \omega^{\mu \cdot 2}`$.
   - **Bounding $`\mathrm{lh}(\mu)`$ by Def 4.1.**
     $`\delta=(\lambda_\mu)^* \lt \omega^{\mu \cdot 2}`$.
     - If $`\delta \le \mu`$: $`\mathrm{lh}(\mu)=\mu+\lambda_\mu`$.
     - Otherwise every element $`\delta_i`$ of the $`\mu`$-localization lies in
       $`(\mu,\omega^{\mu \cdot 2})\subseteq(\mu,\varepsilon_{\mu+1})`$. So $`\delta_i`$
       is non-epsilon, $`\delta_i=\omega^x`$ with $`x \lt \mu \cdot 2`$, and by Thm 2.2
       $`\mathrm{lh}(\delta_i)=\delta_i+\mathrm{logend}(x)\lt \omega^{\mu \cdot 2}`$.
     - In all cases $`\mathrm{lh}(\mu)\lt \omega^{\mu \cdot 2}`$, since
       $`\omega^{\mu \cdot 2} \in P`$.
4. **Conclusion.** Steps 2 and 3 exclude every epsilon $`\mu \lt \Gamma_0`$. So
   $`\mu=\Gamma_0`$. ∎

Also done by hand, with the same pattern of argument: $`N=\varepsilon_0`$,
$`\varepsilon_1`$, $`\varepsilon_{\varepsilon_0}`$ (below).

**Case $`N`$ epsilon, general (OPEN; Route B only, not needed for the Main Theorem).**

- What is needed: $`o(N)`$ is the least epsilon number $`\mu`$ above the fixed part
  $`Q \cap o(N)`$ whose $`\le_1`$-type over that part and whose reach structure
  $`h[Q \cap[o(N),\infty)]`$ match those of $`o(N)`$.
- Examples done by hand with Wilken's $`\mathrm{lh}`$ formulas:
  - $`N=\varepsilon_0`$: $`\mu \le_1 \mu \cdot 2`$ forces $`\mu \in E`$, so
    $`\mu \ge \varepsilon_0`$.
  - $`N=\varepsilon_1`$: the anchor $`\varepsilon_0`$ and $`\varepsilon_0 \cdot 2`$ are
    fixed, so $`\mu \in E \cap(\varepsilon_0 \cdot 2,\varepsilon_1]`$, so
    $`\mu=\varepsilon_1`$.
  - $`N=\varepsilon_{\varepsilon_0}`$ (no anchor; bar = 1, see [§11.4](PROOF-2.md)):
    $`\mu \le_1 \mu \cdot 2+\varepsilon_0`$. For $`\mu=\vartheta(\Omega+\eta)`$ with
    $`\Delta=\Omega`$ this gives $`\mathrm{logend}(\eta)\ge \varepsilon_0`$, so
    $`\eta \ge \varepsilon_0`$ and $`\mu \ge \varepsilon_{\varepsilon_0}`$. Here the element
    $`\varepsilon_0`$ enters through $`\mathrm{lh}`$. It is needed for $`\mathrm{lh}`$-closure,
    not for bar.
- In general this is exactly [W07b, Claims 5.5(b), 5.6]: the witness sets that pin down
  $`\alpha`$ from below, built from $`\bar\alpha`$ ([W07a, Lemma 8.2]). It needs the
  $`\vartheta`$-translation of §4.5.

**Prop 6.5 (PROVED from S1, 2.4, L, C1).**

- (a) $`f \le o`$ (Cor 5.2).
- (b) If $`f`$ is strictly increasing on $`(\mathrm{Std},\lt_p)`$, then $`f=o`$.

<em>Proof of (b).</em> Put $`f(\emptyset):=0`$. Then $`f`$ is strictly increasing on the nodes,
since $`f \ge 1`$ on $`\mathrm{Std}`$. A strictly increasing map of a well-order into
$`\mathrm{On}`$ dominates the rank, so $`f(M)\ge \mathrm{otp}\{N \lt_p M\}=o(M)`$
(Lemma 1.1(c)). Together with (a), $`f=o`$. ∎

So, given L, the **order half of the conjecture already implies the surjectivity half**, and
the Main Theorem.

**Lemma 6.2 (superseded; $`o[V]`$ isominimal via [CW12, Cor 6.3] and closure under bar).**
This route became Route A (Thm 11.1), which is the route used now. It is no longer needed.

---

## 7. Conclusion

**Theorem 7.1 (PROVED from [TR](TR.md), [COMB](COMB.md) and the citations; M1).** For every
$`M \in \mathrm{Std}`$, $`\iota(\Phi(M))=o(M)`$.

1. **L.**
   - §4.2 handles $`N=1`$.
   - Lemma 4.2 handles non-epsilon $`N`$.
   - Prop 4.3 handles epsilon $`N`$. It uses:
     - E1 ([§12.5](PROOF-2.md), from CI and TR);
     - E2 ([§14.3](PROOF-3.md), from PL, TR and [W07b] Cor 5.9, inside the induction of Prop 4.3, M7);
     - [COMB](COMB.md) T.
2. **Finiteness.** $`V_M`$ is finite (Thm VF, [§15.1](PROOF-4.md)).
3. **Embedding.** $`o{\restriction}V_M`$ is an isomorphism of $`\Phi(M)`$ onto a finite
   closed substructure of $`R_1`$ (Lemma 5.1).
4. **Bar-closure.**
   - Non-epsilon one-term nodes: [§11.3](PROOF-2.md) (with M11).
   - Epsilon one-term nodes: $`\mathrm{Bar}_T`$ ([§14.2](PROOF-3.md)) and TR. $`V_M`$ is closed under
     anchor.
5. **Route A.** Thm 11.1 ([CW12] Thm 6.2, Cor 6.3(1), Lemma 6.1) gives
   $`\iota(\Phi(M))=o(M)`$. The case $`M=(0,0)`$ is covered directly ([§11.2](PROOF-2.md), M3).

Route B (Thm 6.3 with Lemma 6.4) is not used.

**Cor 7.2 (PROVED).**

- (a) $`M \lt_p M' \iff \iota(\Phi(M))\lt \iota(\Phi(M'))`$.
- (b)
  $`\{\iota(\Phi(M))\}=[1,\psi_0(\Omega_\omega))=\mathrm{Core}(R_1)\setminus \{0\}`$,
  by C3.
  - The equality with $`\mathrm{Core} \setminus \{0\}`$ uses the outside assumption M13
    (§1.4): the Lean constant `Ord.psi (Ord.Omega ω) 0` is Buchholz's
    $`\psi_0(\Omega_\omega)`$.

<em>Proof.</em> (a) follows from Thm 7.1 and Lemma 1.1(a). (b) follows from Thm 7.1, Lemma 1.1(b)
(range of $`o`$ = $`[1,\psi_0(\Omega_\omega))`$ on $`\mathrm{Std}`$), and C3. ∎

**Prop 7.3 (PROVED from L and C1; justification corrected, M12).** Assume L. Then the order
half of the conjecture already implies Theorem 7.1. Hence the conjecture is equivalent to
Theorem 7.1.

- (⇐) This is Cor 7.2.
- (⇒) Suppose $`\iota \circ \Phi`$ is strictly increasing on $`(\mathrm{Std},\lt_p)`$.
  Prop 6.5(b) (which uses L via Lemma 5.1, and C1) gives $`\iota \circ \Phi=o`$.
- Uniqueness of order isomorphisms alone is not enough. It needs the image to be the same
  initial segment, and the order half does not state that.

This proposition is not used in the main chain.

---

## 8. Corrections and additions to POR.md's definition

- **A1–A5:**
  - A1: multi-root $`M`$;
  - A2: the offset $`1+\mathrm{val}`$;
  - A3: the full addition graph;
  - A4: reflexivity of $`\le_1`$;
  - A5: anchor $`\ne`$ bar, e.g. $`\varepsilon_{\varepsilon_0}`$. **Corrected:**
    $`\mathrm{bar}(\varepsilon_{\varepsilon_0})=1`$, not $`\varepsilon_0`$. By
    [CW12, Def 5.1], $`\varepsilon_{\varepsilon_0}=\vartheta(\Omega+\varepsilon_0)`$ with
    $`\eta'=0`$ and $`\eta_0=\varepsilon_0 \ne 1`$, and $`\eta'=0`$ is not below the
    empty supremum. So $`\bar\alpha`$ is the localization predecessor $`\alpha_{n-1}`$. The
    localization is $`(1,\varepsilon_{\varepsilon_0})`$, because
    $`\varepsilon_0=\vartheta(\Omega)`$ has the smaller argument ([W07a, Def 4.6]). So
    $`\varepsilon_{\varepsilon_0}`$ has no anchor and bar = 1: this is consistent, not a
    mismatch. See [§11.4](PROOF-2.md).
- **A6. Termination of $`\mathrm{lh}_\Phi`$ (T) is not argued in [POR.md](../POR.md).** It is
  now PROVED in [COMB](COMB.md) §8.
  - A $`y=1`$ column inside a $`y \ge 2`$ subtree makes $`\mathrm{Coll}_A`$ re-insert all
    of $`A`$. So the maximum $`y`$ of the last-child subtree is not a decreasing measure.
  - Wilken's corresponding induction is on $`\mathrm{ht}^\tau`$ and uses the translation.
- **A7. $`\log`$ must use CNF addition (absorption).** [POR.md](../POR.md) §3.2 writes it
  with $`+`$ and [phi.py](../por/phi.py) uses `addall`, so both are consistent. A
  concatenating reading would break Lemma R. Example in §4.1.
- **A8. [POR.md](../POR.md) §3.4 already takes $`A`$ to be all children,
  $`(C_1..C_k)`$.** This is the correct reading: $`\mathrm{Coll}`$ of a childless $`y=1`$
  column is $`N`$ itself. This is needed for
  $`\varphi(2,0)=\vartheta(\Omega+\Omega)`$ to get $`\lambda=\alpha \cdot 2`$ (§4.5
  table). No change is needed; this is a confirmation.
- No counterexample to $`\Phi`$ was found in any test.

---

## 9. Numerical checks

The numerical checks were made with scripts that are not published; only
[phi.py](../por/phi.py), [pss.py](../por/pss.py) and [tr.py](../por/tr.py) are in this
repository.

| test | size | failures |
|---|---|---|
| E: re-pointing, $`\iota(\Phi(M)\text{ at } x)=\iota(\Phi(x))`$ | 1,244,496 checks | 0 (6 poral crashes) |
| M: reach maximality | 74,595 roots | 0 |
| R: $`o(N)=\omega^{o(\mathcal{L} N)}`$ via poral exp | 26,328 + 48,267 (overlapping) | 0 |
| $`\mathcal{L}`$ strictly increasing, images standard | 3,882 roots | 0 |
| E2 inside $`\Phi`$ | 40,258 jumps / 17,798 $`\beta`$ | 0 |
| J: E2 semantic (C2 on the closure plus a fresh $`b`$ in every gap) | 40,350 jumps, 89,710 gap tests | 0 (808 poral crashes in gap tests) |
| no-absorption check for bar ([§11.3](PROOF-2.md)) | 23,724 non-epsilon roots | informational: 348 absorb, 160 absorb the last child (the M-case) |
| S1 | 5,292 + 59,863 | 0 |
| Lemma 2.4 | 125,173 nodes | 0 |

[poral](https://github.com/semitrivial/poral) was used only as an external program (new,
compare, exp); none of its code was copied.

---

## 10. What a Lean formalization would need

- **Now provable in Lean:**
  - Lemmas 2.1, 2.2, Cor 2.3 (given S1);
  - Prop 4.1;
  - Lemma 4.2 and Lemma F, given Thm 2.2 and Lemmas 3.3 and 3.4 of [W07b] as axioms. These
    three are notation-free statements about $`\le_1`$ on ordinals.
  - Prop 4.3; Thm 6.3; Lemma 6.4 (non-epsilon); Prop 6.5; Prop 7.3;
  - Lemma 6.1; Thm 11.1; Thm VF ([§15.1](PROOF-4.md)), given the cited facts.
- **Axioms (cited):**
  - [C01, Thm 5.9(1), (2), (4)];
  - [C01, Thm 5.12] and [W07b, Cor 5.10] (core);
  - [W07b, Lemma 2.1, Thm 2.2, Lemmas 3.3, 3.4].
  - [W07b, Thm 5.3] only when E1 is proved through $`\vartheta`$.
- **Definitions needed:** $`\le_1`$ on ordinals, via the finite-set criterion or directly.
  Covers, closed sets, $`P^*`$, $`\iota`$.
- **The earlier list of open research items: all superseded.**
  - Now PROVED on paper: E1 and E2 ([§12.5](PROOF-2.md), [§14.3](PROOF-3.md)), R, T, S1 and Lemma 2.4
    ([COMB](COMB.md)), and TR ([TR](TR.md)).
  - Not needed: Lemma 6.4 for epsilon $`N`$ (Route B).
  - For Lean, the chain of §0 also needs:
    - [CW12] Thm 6.2 and Cor 6.3 (1), (2), and Lemma 5.10, as axioms;
    - [W07a] Lemmas 3.30, 4.3–4.5, 4.9, 6.3–6.5, Cor 7.3, Cor 7.6, as axioms or through a
      formal $`T^1`$;
    - the syntactic lemmas of [§13](PROOF-3.md)–[§15](PROOF-4.md) by structural induction.

---

**Part 1: §0–§10** | [Part 2: §11–§12](PROOF-2.md) | [Part 3: §13–§14](PROOF-3.md) | [Part 4: §15–§16, References, Review history](PROOF-4.md)
