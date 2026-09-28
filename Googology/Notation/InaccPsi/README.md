[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# InaccPsi: Buchholz's $`\psi`$ over the first $`\omega`$ weakly inaccessible cardinals

This directory defines an ordinal collapsing function over $`\omega`$ weakly inaccessible
cardinals $`I_0 \lt I_1 \lt \cdots`$ and their supremum $`I_\omega`$, and a notation system for it.

- **Base.** The collapsing function over one weakly inaccessible cardinal $`I`$ is
  Definition 4.2 of W. Buchholz, *A simplified version of local predicativity*
  (in P. Aczel, H. Simmons, S. S. Wainer (eds.), *Proof Theory*, Cambridge University
  Press 1992, 115–147). W. Pohlers, *Subsystems of set theory and second order number
  theory* (Handbook of Proof Theory, Elsevier 1998, Chapter IV), §3.4.4, presents the
  same definition together with the facts (155)–(179) and a sketch of the term system.
- **Extension.** The extension to $`\omega`$ weakly inaccessible cardinals is new here (koteitan
  and Claude). G. Wilken, *A glimpse of Σ₃-elementarity* (2020), p. 421, claims without
  a definition that "the Skolem-hull notation system derived from the first ω-many
  weakly inaccessible cardinals" covers the core of $`R_2^+`$. The system here is one way to
  make that phrase precise; nothing says that it is the system Wilken had in mind.

## 1. Hypotheses and notation

- $`\Omega_0 = 0`$ and $`\Omega_\xi = \omega_\xi`$ (the ordinal of $`\aleph_\xi`$) for $`\xi \ge 1`$. So $`\xi \mapsto \Omega_\xi`$ enumerates
  $`\{0\}`$ and the uncountable cardinals. It is strictly increasing and continuous.
- $`\varphi (\xi, \eta)`$ is the binary Veblen function, $`\varphi (0, \eta) = \omega^\eta`$. $`1 = \varphi (0, 0)`$.
- $`\mathrm{SC}`$ is the class of strongly critical ordinals: $`\gamma \gt 0`$ with $`\varphi (\xi, \eta) \lt \gamma`$ for all
  $`\xi, \eta \lt \gamma`$. Every uncountable cardinal is in $`\mathrm{SC}`$.
- **Hypothesis.** $`I : \mathbb{N} \to \mathrm{Ord}`$ is strictly increasing, and every $`I_n`$ is an uncountable
  regular cardinal with $`\Omega_{I_n} = I_n`$ (a weakly inaccessible cardinal). We put
  $`I_\omega = \sup_n I_n`$; then also $`\Omega_{I_\omega} = I_\omega`$. We do **not** assume that the $`I_n`$ are
  the first $`\omega`$ weakly inaccessible cardinals: nothing below needs it.
- $`R = \{I_n \mid n \lt \omega \} \cup \{\Omega_{s+1} \mid s \in \mathrm{Ord}\}`$. Every member of $`R`$ is an uncountable regular
  cardinal. These are the subscripts at which $`\psi`$ collapses.

## 2. The definition

By recursion on $`\alpha`$, define sets $`\mathrm{Cl}(\alpha, \beta)`$ and ordinals $`\psi_\kappa (\alpha)`$ ($`\kappa \in R`$):

- $`\mathrm{Cl}(\alpha, \beta)`$ is the least set $`X`$ such that
  - $`\beta \subseteq X`$, $`0 \in X`$, $`I_n \in X`$ for every $`n \lt \omega`$, and $`I_\omega \in X`$;
  - $`\xi, \eta \in X`$ $`\Rightarrow`$ $`\xi + \eta \in X`$, $`\varphi (\xi, \eta) \in X`$, $`\Omega_\xi \in X`$;
  - $`\xi, \pi \in X`$, $`\xi \lt \alpha`$, $`\pi \in R`$ $`\Rightarrow`$ $`\psi_\pi (\xi) \in X`$.
- $`\psi_\kappa (\alpha) = \min \{\beta \mid \kappa \in \mathrm{Cl}(\alpha, \beta) \land \mathrm{Cl}(\alpha, \beta) \cap \kappa \subseteq \beta \}`$.

For one inaccessible $`I`$ (all $`I_n`$ equal to $`I`$, no $`I_\omega`$) this is Buchholz's
definition. The only changes are the constants $`I_n`$, $`I_\omega`$ and the subscript class $`R`$.

## 3. Facts about $`\psi`$

$`\kappa`$ ranges over $`R`$. The numbers in brackets are Pohlers's.

**F1 (monotone).** $`\alpha \le \alpha '`$ and $`\beta \le \beta '`$ $`\Rightarrow`$ $`\mathrm{Cl}(\alpha, \beta) \subseteq \mathrm{Cl}(\alpha ', \beta ')`$. [155]

**F2 (size).** $`\lvert \mathrm{Cl}(\alpha, \beta)\rvert \le \max(\lvert \beta \rvert, \aleph_0)`$. [157] — The set is the union of $`\omega`$
stages; each stage applies finitely many finitary operations to the previous one and
adds $`\omega + 1`$ constants.

**F3.** $`\kappa \in \mathrm{Cl}(\alpha, \beta)`$ for some $`\beta \lt \kappa`$. — If $`\kappa = I_n`$ it is a constant. If
$`\kappa = \Omega_{s+1}`$ take $`\beta = s + 1 \lt \kappa`$: then $`s \in \mathrm{Cl}`$, $`s + 1 = s + \varphi (0,0) \in \mathrm{Cl}`$,
$`\Omega_{s+1} \in \mathrm{Cl}`$.

**F4 (collapsing).** $`\psi_\kappa (\alpha) \lt \kappa`$, $`\kappa \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$, $`\mathrm{Cl}(\alpha, \psi_\kappa (\alpha)) \cap \kappa \subseteq \psi_\kappa (\alpha)`$,
and $`\psi_\kappa (\alpha) \notin \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$. [160] — Start from the $`\beta_0 \lt \kappa`$ of F3 and put
$`\beta_{n+1} = \sup(\mathrm{Cl}(\alpha, \beta_n) \cap \kappa)`$. By F2 and the regularity of $`\kappa`$, $`\beta_{n+1} \lt \kappa`$. Then
$`\beta = \sup_n \beta_n \lt \kappa`$ (as $`\operatorname{cf} \kappa \gt \omega`$) satisfies the condition, since $`\mathrm{Cl}(\alpha, \beta)`$ is the
union of the $`\mathrm{Cl}(\alpha, \beta_n)`$. The last claim: $`\psi_\kappa (\alpha) \in \mathrm{Cl} \cap \kappa \subseteq \psi_\kappa (\alpha)`$ is impossible.

**F5.** $`\alpha_0 \lt \alpha`$ and $`\alpha_0 \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$ $`\Rightarrow`$ $`\psi_\kappa (\alpha_0) \lt \psi_\kappa (\alpha)`$. [161] — $`\psi_\kappa (\alpha_0)`$ is in
$`\mathrm{Cl}(\alpha, \psi_\kappa (\alpha)) \cap \kappa \subseteq \psi_\kappa (\alpha)`$, and it is not $`\psi_\kappa (\alpha)`$ by F4.

**F6.** $`\psi_\kappa (\alpha) \in \mathrm{SC}`$. [163] — $`0 \in \mathrm{Cl} \cap \kappa`$ gives $`\psi_\kappa (\alpha) \gt 0`$; for $`\xi, \eta \lt \psi_\kappa (\alpha)`$,
$`\varphi (\xi, \eta) \in \mathrm{Cl} \cap \kappa`$ because $`\kappa \in \mathrm{SC}`$.

**F7 (cardinals).** $`\Omega_\sigma \in \mathrm{Cl}(\alpha, \beta)`$ $`\Rightarrow`$ $`\sigma \in \mathrm{Cl}(\alpha, \beta)`$. [164] — By induction on the
generation of $`x \in \mathrm{Cl}(\alpha, \beta)`$: if $`x = \Omega_\sigma`$ then $`\sigma \in \mathrm{Cl}(\alpha, \beta)`$.
- $`x \lt \beta`$: $`\sigma \le \Omega_\sigma \lt \beta`$.
- $`x \in \{0, I_n, I_\omega \}`$: $`\Omega`$ is injective and these are fixed points of $`\Omega`$, so $`\sigma = x`$.
- $`x = \xi + \eta`$: $`\Omega_\sigma`$ is $`0`$ or additively principal, so $`\eta = \Omega_\sigma`$ or $`\eta = 0 \land \xi = \Omega_\sigma`$.
- $`x = \varphi (\xi, \eta)`$: $`\Omega_\sigma \in \mathrm{SC}`$ (or $`\sigma = 0`$), so $`\xi = \Omega_\sigma`$ or $`\eta = \Omega_\sigma`$.
- $`x = \Omega_\xi`$: $`\xi = \sigma`$.
- $`x = \psi_\pi (\xi)`$: if $`\sigma = \Omega_\sigma`$ then $`\sigma = x \in \mathrm{Cl}`$. Otherwise $`\sigma \lt \Omega_\sigma = \psi_\pi (\xi) =: \gamma`$, so
  $`\sigma \in \gamma \subseteq \mathrm{Cl}(\xi, \gamma)`$, hence $`\Omega_\sigma \in \mathrm{Cl}(\xi, \gamma) \cap \pi \subseteq \gamma`$, i.e. $`\gamma \lt \gamma`$. Impossible.

**F8 (successors).** $`s + 1 \in \mathrm{Cl}(\alpha, \beta)`$ $`\Rightarrow`$ $`s \in \mathrm{Cl}(\alpha, \beta)`$. — Same induction:
$`\xi + \eta = s + 1`$ with $`\eta \ne 0`$ forces $`\eta = t + 1`$, $`s = \xi + t`$; $`\varphi`$-values that are
successors equal $`1`$; $`\Omega`$-values and $`\psi`$-values are $`0`$ or limits (F6).

**F9 (successor subscripts).** For $`\kappa = \Omega_{s+1}`$: $`\Omega_s \lt \psi_\kappa (\alpha) \lt \Omega_{s+1}`$, so $`\psi_\kappa (\alpha)`$
is not a cardinal (for $`s = 0`$: $`\psi_\kappa (\alpha)`$ is countable). [167] — $`\kappa \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$
(F4), so $`s + 1`$ and $`s`$ are in it (F7, F8). As $`s \lt \kappa`$, $`s \in \mathrm{Cl} \cap \kappa`$, so `Ω_s ∈ Cl ∩ κ
⊆ $`\psi`$_κ(α)`.

**F10 (inaccessible subscripts).** For $`\kappa = I_n`$: $`\Omega_{\psi_\kappa (\alpha)} = \psi_\kappa (\alpha)`$, and
$`I_{n-1} \lt \psi_\kappa (\alpha) \lt I_n`$ when $`n \ge 1`$ ($`\Omega_1 \lt \psi_\kappa (\alpha)`$ when $`n = 0`$). [170] — $`I_{n-1}`$
(resp. $`\Omega_1`$) is in $`\mathrm{Cl} \cap \kappa`$. For the fixed point: let $`\gamma = \psi_\kappa (\alpha)`$ and
$`\Omega_\sigma \le \gamma \lt \Omega_{\sigma +1}`$. $`I_n`$ is a limit cardinal, so $`\Omega_{\sigma +1} \lt I_n`$, hence
$`\Omega_{\sigma +1} \notin \mathrm{Cl}(\alpha, \gamma)`$ (else $`\Omega_{\sigma +1} \lt \gamma`$), hence $`\sigma \notin \mathrm{Cl}(\alpha, \gamma)`$, hence $`\sigma \ge \gamma`$. So
$`\Omega_\sigma \ge \sigma \ge \gamma \ge \Omega_\sigma`$: $`\gamma = \sigma = \Omega_\sigma`$.

**F11 (monotone in the argument).** $`\xi \le \alpha`$ $`\Rightarrow`$ $`\psi_\kappa (\xi) \le \psi_\kappa (\alpha)`$ and
$`\mathrm{Cl}(\xi, \psi_\kappa (\xi)) \subseteq \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$. [168] — $`\kappa \in \mathrm{Cl}(\xi, \psi_\kappa (\alpha))`$: for $`\kappa = I_n`$ it is a
constant; for $`\kappa = \Omega_{s+1}`$, $`s \lt \Omega_s \lt \psi_\kappa (\alpha)`$ (F9). And
$`\mathrm{Cl}(\xi, \psi_\kappa (\alpha)) \cap \kappa \subseteq \mathrm{Cl}(\alpha, \psi_\kappa (\alpha)) \cap \kappa \subseteq \psi_\kappa (\alpha)`$.

**F12 (strictly monotone at normal arguments).** If $`\alpha_0 \lt \alpha`$ and
$`\alpha_0 \in \mathrm{Cl}(\alpha_0, \psi_\kappa (\alpha_0))`$, then $`\psi_\kappa (\alpha_0) \lt \psi_\kappa (\alpha)`$. — By F11 $`\alpha_0 \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$; apply F5.

## 4. The term system

### Terms

```math
t \mathrel{::=} 0 \mid I_n \mid I_\omega \mid t + t \mid \varphi(t, t) \mid \Omega_t \mid \psi^S_s(t) \mid \psi^I_n(t) \qquad (n \in \mathbb{N})
```

$`\psi^S_s(a)`$ denotes $`\psi_{\Omega_{s+1}}(a)`$ and $`\psi^I_n(a)`$ denotes $`\psi_{I_n}(a)`$. The value
$`\lvert t\rvert`$ of a term is the obvious ordinal. Subscripts are not general terms: a subscript in
$`R`$ is either a successor cardinal, given by $`s`$, or an $`I_n`$, given by $`n`$.

### Kinds

- **SC terms**: $`I_n`$, $`I_\omega`$, $`\Omega_a`$, $`\psi^S_s(a)`$, $`\psi^I_n(a)`$.
- **principal terms**: SC terms and $`\varphi (a, b)`$.
- **fixed-point terms** $`F`$: $`I_n`$, $`I_\omega`$, $`\psi^I_n(a)`$ (values $`x`$ with $`\Omega_x = x`$).
- **cardinal terms** $`K`$: $`F`$ and $`\Omega_a`$.

### Normal forms $`\mathrm{NF}`$

- $`0`$, $`I_n`$, $`I_\omega`$ are in $`\mathrm{NF}`$.
- $`a + b`$ is in $`\mathrm{NF}`$ iff $`a`$ is a principal $`\mathrm{NF}`$ term, $`b \ne 0`$ is in $`\mathrm{NF}`$, and the first
  summand of $`b`$ is $`\le a`$.
- $`\varphi (a, b)`$ is in $`\mathrm{NF}`$ iff $`a, b \in \mathrm{NF}`$, $`a \lt \varphi (a, b)`$ and $`b \lt \varphi (a, b)`$.
- $`\Omega_a`$ is in $`\mathrm{NF}`$ iff $`a \in \mathrm{NF}`$, $`a \ne 0`$ and $`a \notin F`$.
- $`\psi^S_s(a)`$ is in $`\mathrm{NF}`$ iff $`s, a \in \mathrm{NF}`$ and $`K_{\psi^S_s(a)}(a) \lt a`$.
- $`\psi^I_n(a)`$ is in $`\mathrm{NF}`$ iff $`a \in \mathrm{NF}`$ and $`K_{\psi^I_n(a)}(a) \lt a`$.

Here $`\lt`$ is the comparison below, and $`K_\mu (a) \lt a`$ means that every member of the
finite set $`K_\mu (a)`$ is $`\lt a`$.

### The set $`K_\mu (a)`$

For a term $`\mu`$, $`K_\mu (a)`$ is the finite set of arguments of the collapses in $`a`$ that are
not below $`\mu`$ (Pohlers's Definition 3.4.4.2):

- $`K_\mu (0) = K_\mu (I_n) = K_\mu (I_\omega) = \emptyset`$;
- $`K_\mu (a + b) = K_\mu (a) \cup K_\mu (b)`$, $`K_\mu (\varphi (a, b)) = K_\mu (a) \cup K_\mu (b)`$;
- for an SC term $`a \lt \mu`$: $`K_\mu (a) = \emptyset`$;
- for $`a \ge \mu`$: $`K_\mu (\Omega_b) = K_\mu (b)`$, $`K_\mu (\psi^S_s(b)) = \{b\} \cup K_\mu (s) \cup K_\mu (b)`$,
  $`K_\mu (\psi^I_n(b)) = \{b\} \cup K_\mu (b)`$.

**Soundness (the easy half of Pohlers's (178)).** If $`a \in \mathrm{NF}`$ and every member of
$`K_\mu (a)`$ is $`\lt \alpha`$, then $`\lvert a\rvert \in \mathrm{Cl}(\alpha, \lvert \mu \rvert)`$. — Induction on $`a`$; each clause of $`K`$
matches a clause of $`\mathrm{Cl}`$. The other half is not needed for the well-ordering.

It follows that $`\psi^S_s(a) \in \mathrm{NF}`$ gives $`\lvert a\rvert \in \mathrm{Cl}(\lvert a\rvert, \psi_{\Omega_{\lvert s\rvert +1}}(\lvert a\rvert))`$, and
$`\psi^I_n(a) \in \mathrm{NF}`$ gives $`\lvert a\rvert \in \mathrm{Cl}(\lvert a\rvert, \psi_{I_n}(\lvert a\rvert))`$. So F12 applies to the arguments of
normal collapses. In both cases the bound $`\mu`$ is the collapse term itself, which is not yet
known to be normal; only the direction `cmp x μ = .lt → |x| < |μ|` is used
(`lt_psiS_of_cmp`, `lt_psiI_of_cmp`).

An earlier version used the bound $`\mathrm{card}(\Omega_s)`$ for $`\psi^S_s(a)`$. That condition is too strong:
for $`s = \psi^I_0(I_0)`$ the ordinal $`\psi_{\Omega_{\lvert s\rvert +1}}(\lvert s\rvert + 1)`$ of $`\bigcup_a \mathrm{Cl}(a, 0)`$ had no normal
form, because $`K_s(s + 1) = \{I_0\}`$ and $`\lvert s\rvert + 1 \lt I_0`$, while $`\lvert s\rvert + 1`$ is the only argument
$`a`$ in its own closure with that value of $`\psi`$.

### The cardinal part $`\mathrm{card}(t)`$

$`\mathrm{card}(t)`$ is a cardinal term or $`0`$, with $`\lvert \mathrm{card}(t)\rvert`$ the cardinality-level of $`\lvert t\rvert`$
(the largest $`\Omega_\sigma \le \lvert t\rvert`$, or $`0`$):

- $`\mathrm{card}(0) = 0`$; $`\mathrm{card}(a + b) = \mathrm{card}(a)`$; $`\mathrm{card}(\varphi (a, b)) = \max(\mathrm{card}(a), \mathrm{card}(b))`$;
- $`\mathrm{card}(t) = t`$ for $`t \in K`$;
- $`\mathrm{card}(\psi^S_s(a)) = \mathrm{card}(\Omega_s)`$, where $`\mathrm{card}(\Omega_s)`$ means $`0`$ if $`s = 0`$, $`s`$ if $`s \in F`$,
  and $`\Omega_s`$ otherwise.

### Comparison

$`a \lt b`$ on terms is defined by recursion on $`\mathrm{size}(a) + \mathrm{size}(b)`$:

1. $`0 \lt b`$ iff $`b \ne 0`$; $`a \lt 0`$ never.
2. Sums (a principal term is a sum with one summand): compare the lists of summands
   lexicographically, a proper prefix being smaller.
3. $`\varphi (a, b)`$ vs $`\varphi (c, d)`$: $`a \lt c \land b \lt \varphi (c, d)`$, or $`a = c \land b \lt d`$, or
   $`c \lt a \land \varphi (a, b) \lt d`$.
4. $`\varphi (a, b)`$ vs an SC term $`s`$ (for strongly critical $`\gamma`$: $`\varphi (\xi, \gamma) = \gamma`$ when $`\xi \lt \gamma`$, and
   $`\varphi (\gamma, 0) = \gamma`$):
   - if $`a \lt s`$: compare $`b`$ with $`s`$;
   - if $`a = s`$: $`\varphi (a, b) = s`$ when $`b = 0`$, and $`\varphi (a, b) \gt s`$ otherwise;
   - if $`a \gt s`$: $`\varphi (a, b) \gt s`$.

   These are identities of ordinals, so they hold for every $`\varphi (a, b)`$, normal or not. The
   $`\mathrm{NF}`$ conditions $`a \lt \varphi (a, b)`$ and $`b \lt \varphi (a, b)`$ exclude $`\varphi (s, 0)`$ and $`\varphi (a, s)`$ with
   $`a \lt s`$.
5. SC terms among themselves:
   - $`\Omega_a \lt \Omega_c`$ iff $`a \lt c`$; for $`f \in F`$: $`\Omega_a \lt f`$ iff $`a \lt f`$, and $`f \lt \Omega_a`$ iff
     $`f \lt a`$;
   - $`I_n \lt I_m`$ iff $`n \lt m`$; $`I_n \lt I_\omega`$; $`\psi^I_n(a) \lt I_m`$ iff $`n \le m`$;
     $`I_m \lt \psi^I_n(a)`$ iff $`m \lt n`$; $`\psi^I_n(a) \lt I_\omega`$;
     $`\psi^I_n(a) \lt \psi^I_m(b)`$ iff $`n \lt m \lor (n = m \land a \lt b)`$;
   - $`\psi^S_s(a) \lt \psi^S_t(b)`$ iff $`s \lt t \lor (s = t \land a \lt b)`$;
   - for a cardinal term $`k`$: $`\psi^S_s(a) \lt k`$ iff $`\mathrm{card}(\Omega_s) \lt k`$, and $`k \lt \psi^S_s(a)`$ iff
     $`k \le \mathrm{card}(\Omega_s)`$.

### Main theorem

On $`\mathrm{NF}`$ terms, $`a \lt b \iff \lvert a\rvert \lt \lvert b\rvert`$. Hence $`\lvert\cdot\rvert`$ is injective on $`\mathrm{NF}`$, and $`(\mathrm{NF}, \lt)`$ is
a strict well-order, isomorphic to a set of ordinals. Proved in `Correct.lean` for every
`InaccSeq`: `Term.cmp_eq_compare`, `Term.eq_of_val_eq`, `Term.isWellOrder_cmp`.

The facts used, by clause:
- 3, 4: the Veblen function (Mathlib) and F6;
- 5, first line: $`\Omega`$ strictly increasing, fixed points;
- 5, second line: F10;
- 5, third and fourth lines: F9 and F12 (through the soundness of $`K`$).

### Completeness

The values of the $`\mathrm{NF}`$ terms are exactly $`\bigcup_a \mathrm{Cl}(a, 0)`$, for every `InaccSeq`
(`Term.vals_eq` in `Onto.lean`). With the main theorem, each member of $`\bigcup_a \mathrm{Cl}(a, 0)`$ is the
value of exactly one $`\mathrm{NF}`$ term (`Term.existsUnique_NF`).

- $`\subseteq`$: each clause of a term is a clause of $`\mathrm{Cl}`$ (`Term.exists_mem_CSet`).
- $`\supseteq`$: induction on $`\mathrm{Cl}`$. For $`x + y`$: `addNF`, which drops the summands of the left term
  below the head of the right one. For $`\varphi (x, y)`$: it is $`x`$, $`y`$, or the normal form
  $`\varphi (a, b)`$. For $`\Omega_x`$: it is $`0`$, $`x`$ (a fixed point of $`\Omega`$), or $`\Omega_a`$.
- For $`\psi_\kappa (\xi)`$: induction on $`\xi`$. Let $`\gamma = \psi_\kappa (\xi)`$ and $`M(\xi) = \min(\mathrm{Cl}(\xi, \gamma) \cap [\xi, \infty))`$. No
  collapse with an argument in $`[\xi, M(\xi))`$ enters $`\mathrm{Cl}(M(\xi), \gamma)`$, so $`\mathrm{Cl}(M(\xi), \gamma) = \mathrm{Cl}(\xi, \gamma)`$,
  $`\psi_\kappa (M(\xi)) = \gamma`$ and $`M(\xi) \in \mathrm{Cl}(M(\xi), \psi_\kappa (M(\xi)))`$ (`psi_M_eq`, `M_mem_self`). $`M(\xi)`$ is
  computed from the parts of $`\xi`$ (`NFM.lean`), with $`R = \mathrm{Cl}(\xi, \gamma)`$:
  - a sum: the leading summand stays when it is in $`R`$; otherwise $`M(x) = M(\text{leading summand})`$;
  - $`M(\Omega_a) = \Omega_{M(a)}`$ (with Pohlers's (172): if $`\mathrm{Cl}(\alpha, \beta)`$ meets $`[\Omega_\sigma, \Omega_{\sigma +1})`$, then
    $`\Omega_\sigma \in \mathrm{Cl}(\alpha, \beta)`$);
  - $`M(\psi_{I_n}(y))`$ is $`\psi_{I_n}(y)`$, $`I_n`$ or $`\psi_{I_n}(M(y))`$;
  - $`M(\psi_{\Omega_{s+1}}(y))`$ is $`\psi_{\Omega_{s+1}}(y)`$, $`\Omega_{s+1}`$, $`\Omega_{M(s)}`$ or $`\psi_{\Omega_{s+1}}(M(y))`$;
  - $`M(\varphi (a, b)) = \varphi (a, M(b))`$ if $`a \in R`$, and $`\varphi (M(a), M(q))`$ otherwise, where $`q`$ is the
    least ordinal with $`b \lt \varphi (M(a), q)`$.

  So $`M(\xi)`$ is a value, using the collapses at arguments below $`\xi`$ only.
- **The converse of the soundness of $`K`$** (the other half of Pohlers's (178)): for
  $`t \in \mathrm{NF}`$, $`\lvert t\rvert \in \mathrm{Cl}(\lvert \alpha \rvert, \lvert \mu \rvert)`$ gives $`K_\mu (t) \lt \alpha`$ (`Term.KLt_complete`). Its collapse case
  is `arg_mem_of_psi_mem`: if $`\psi_\kappa (d) \in \mathrm{Cl}(\alpha, \beta)`$, $`\beta \le \psi_\kappa (d)`$ and $`d \in \mathrm{Cl}(d, \psi_\kappa (d))`$,
  then $`d \in \mathrm{Cl}(\alpha, \beta)`$ and $`d \lt \alpha`$. The closure made $`\psi_\kappa (d)`$ as $`\psi_\kappa (e)`$ with
  $`e \in \mathrm{Cl}(\alpha, \beta)`$, $`e \lt \alpha`$; then $`d = M(e)`$, and $`M`$ does not leave $`\mathrm{Cl}(\alpha, \beta)`$
  (`MQ_of_mem_CSet`). With $`\mu = \psi_\kappa (M(\xi))`$ and
  $`\alpha = M(\xi)`$ it turns $`M(\xi) \in \mathrm{Cl}(M(\xi), \psi_\kappa (M(\xi)))`$ into the $`\mathrm{NF}`$ condition of $`\psi_\kappa (M(\xi))`$.

## 5. What is not done here

- **Completeness** is proved: `Term.vals_eq` (§4). It is stated for $`\bigcup_a \mathrm{Cl}(a, 0)`$; that
  this set equals $`\mathrm{Cl}(\varepsilon_{I_\omega +1}, 0)`$ (or another bounded closure) is not proved.
- **Recursive regular ordinals.** As in Buchholz and Pohlers, the cardinals are true
  cardinals. Replacing them by recursively regular ordinals is not attempted.
- **Wilken's claim.** Whether the countable part of the system covers $`\mathrm{Core}(R_2^+)`$ is
  open, and it cannot be settled by formalizing known mathematics. Wilken states it as a
  claim without proof (*A glimpse of Σ₃-elementarity*, 2020, p. 421, repeated in *Pure
  Σ₂-elementarity beyond the core*, 2021, §1), calls the analysis of $`R_2^+`$ a topic of
  future work, and says that it needs a generalization of ordinal arithmetic whose
  beginning is Weiermann–Wilken 2011. Settling it needs that analysis: an assignment of
  the isominimal realizations of the finite patterns of $`R_2^+ = (\mathrm{Ord}; 0, +; \le, \le_1, \le_2)`$
  to terms of a system such as this one, which no paper provides.

## 6. Files

| file | contents |
|---|---|
| `Hyp.lean` | $`\Omega`$, the hypothesis structure `InaccSeq`, $`R`$, basic facts on cardinals and $`\mathrm{SC}`$ |
| `Ord.lean` | $`\mathrm{Cl}`$, $`\psi`$, F1–F4 |
| `Facts.lean` | F5–F12 |
| `Term.lean` | terms, values, kinds, $`\mathrm{card}`$, $`K`$, the comparison, $`\mathrm{NF}`$ |
| `Correct.lean` | soundness of $`K`$, the main theorem |
| `CNF.lean` | the leading summand, the principal summands `Comp`, and `q0(c, v)`, the least $`q`$ with $`v \lt \varphi (c, q)`$ |
| `Struct.lean` | the bound $`\Lambda`$, (172), the shape of the members of $`\mathrm{Cl}(\alpha, \beta)`$ |
| `NFM.lean` | $`M`$, its computation, $`M`$ does not leave $`\mathrm{Cl}(\alpha, \beta)`$, `arg_mem_of_psi_mem` |
| `Onto.lean` | the converse of the soundness of $`K`$, `addNF`, completeness: `Term.vals_eq`, `Term.existsUnique_NF` |
