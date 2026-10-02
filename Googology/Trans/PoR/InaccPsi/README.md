[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/PoR/InaccPsi: Wilken's claim on the core of $`R_2^+`$

Patterns of resemblance → terms of [InaccPsi](../../../Notation/InaccPsi/README.md) (Buchholz's
$`\psi`$ over $`\omega`$ weakly inaccessible cardinals). This directory records the work on a claim of
G. Wilken: what the claim says, what is proved, what is open, and the experiments.

Status words: **Lean** (checked by Lean, no `sorry`, only the axioms `propext`, `Classical.choice`,
`Quot.sound`); **proved** (on paper, and an independent referee found it proved with no fatal or
blocking point); **cited** (a paper and the place); **checked** (computed on finitely many cases);
**conjecture**; **open**.

## 1. The claim and its source

G. Wilken, "A glimpse of Σ₃-elementarity" (2020), pp. 420–421, repeated in G. Wilken, "Pure
Σ₂-elementarity beyond the core" (APAL 172, 2021), §1:

> We claim that the segment of countable ordinals denoted by the Skolem-hull notation system
> derived from the first ω-many weakly inaccessible cardinals covers (the domain of) Core(R2+).

Here $`R_2^+ = (\mathrm{Ord}; 0, +, \le, \le_1, \le_2)`$, and the core is the union of the least
(isominimal) realizations of its finite patterns. Wilken adds that the system for one weakly
inaccessible cardinal matches the ordinal of the set theory KPI, and that the analysis of $`R_2^+`$
is future work which needs the arithmetic begun in Weiermann–Wilken, "Ordinal arithmetic with
simultaneously defined θ-functions" (MLQ 57, 2011). On p. 438 of the 2020 paper he says that the
core of $`R_2^+`$ "will be shown" to be an initial segment. No definition of the notation system and
no proof is in the papers we have.

## 2. Our precise statement

This section is our reading of the claim. It has no referee; it fixes three choices.

**(a) What "covers" means.** In the same paragraph Wilken says that the cores of $`R_1^+`$ and
$`R_2`$ "cover the same initial segment", that is, they are that segment. So the strongest reading is
equality of sets, $`\mathrm{Core}(R_2^+) = \rho`$, where $`\rho`$ is the set of countable values of the
notation system. The two halves are the upper bound $`\mathrm{Core}(R_2^+) \subseteq \rho`$ and the lower
bound $`\rho \subseteq \mathrm{Core}(R_2^+)`$.

**(b) Which $`R_2^+`$.** Wilken defines $`\le_i`$ by $`\Sigma_i`$-elementarity; we write $`R_2^S`$.
Carlson, "Patterns of resemblance of order 2" (APAL 158, 2009), Defs 5.3–5.4, defines it by coverings;
we write $`R_2^C`$. They are proved equal only below $`\upsilon_{\omega\cdot\omega}`$ (Theorem EQB in
[R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md)), far below every candidate for $`\rho`$. We take $`R_2^C`$
first, because its core is known to be an initial segment: by Carlson 2009, Thm 14.14, it is the least
$`\kappa`$ with $`\kappa \le_1 \beta`$ for all $`\beta \ge \kappa`$. Then the claim reads
$`\rho \le_1 \beta`$ for all $`\beta \ge \rho`$ (upper bound) and no smaller ordinal has this property
(lower bound). $`R_2^S`$ comes second.

**(c) Which notation system.** What matters is the bound $`X`$ on the arguments of the collapses.
Write $`\rho_X`$ for the countable values of the InaccPsi terms whose collapse arguments are all below
$`X`$. Three candidates:

| reading | bound | countable part |
|---|---|---|
| A (first choice) | $`I_\omega`$ | $`\rho_A = \psi_{\Omega_1}(I_\omega)`$ |
| B | $`\varepsilon_{I_\omega+1}`$ | $`\rho_B = \psi_{\Omega_1}(\varepsilon_{I_\omega+1})`$ |
| S (the whole system) | none | $`\rho_S = \psi_{\Omega_1}(\Lambda)`$, $`\Lambda`$ the least $`\alpha \gt I_\omega`$ with $`\Omega_\alpha = \alpha`$ |

Lean proves $`\rho_A \lt \rho_B \lt \rho_S`$, so at most one reading can hold with equality. We take
A first: Wilken's own systems $`T^\tau`$ are unions of systems of finite level, and the countable part
of such a union is the collapse of the supremum. Also
$`\sup_k \psi_{\Omega_1}(I_k) = \sup_k \psi_{\Omega_1}(\varepsilon_{I_k+1}) = \psi_{\Omega_1}(I_\omega)`$
(continuity, Lemma CONT below), so A fits the remark on KPI too. That other standard systems give the same
countable ordinal at the same bound is a conjecture.

So the main statement is, in $`R_2^C`$ and reading A:

```math
\mathrm{Core}(R_2^C) = \psi_{\Omega_1}(I_\omega) = \{\, |t| : t \text{ an InaccPsi normal form, all collapse arguments } \lt I_\omega,\ |t| \lt \Omega_1 \,\}.
```

Both halves are **open**.

## 3. What is proved

**Lean** (the three files of this directory, built with the library):

- **Lemma L** (`CSet_inter_Om1`). For every $`\alpha`$: $`\mathrm{Cl}(\alpha, 0) \cap \Omega_1 = \psi_{\Omega_1}(\alpha)`$ as sets.
  So the countable values of the terms bounded by $`X`$ are exactly the ordinals below
  $`\psi_{\Omega_1}(X)`$ (`bounded_inter_Om1`), and those of the whole system are the ordinals below
  $`\psi_{\Omega_1}(\Lambda)`$ (`vals_inter_Om1`, `CSet_sub_Lam`). Each set is an initial segment of $`\Omega_1`$.
- **The three bounds** (`three_bounds`). $`\rho_A \lt \rho_B \lt \rho_S`$.
- **Lemma IS** (`lt_psi_one_mem_Vals`, `exists_NF_of_lt_psi_one`, `mem_Vals_of_lt_of_countable`). Every ordinal
  below $`\psi_{\Omega_1}(a)`$ is the value of a normal form; the countable values are downward closed.
  Proof idea: the least non-value $`\rho`$ is closed under $`+`$ and $`\varphi`$, and satisfies the defining
  condition of every $`\psi_{\Omega_1}(a)`$.
- **Lemma CONT** (`psi_one_iSup`). For increasing $`a_n`$: $`\psi_{\Omega_1}(\sup_n a_n) = \sup_n \psi_{\Omega_1}(a_n)`$.
- **Seven terms** (`LowTerms.lean`). For $`\eta \in \{0, 1, 2, \omega, \omega+1, \omega\cdot 2, \omega^2\}`$ the term
  $`u(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ with $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$ is a normal form, has
  this value, and the seven values increase; also $`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$.

**Proved on paper and refereed:**

- **Theorem CORE-C.** Every ordinal below $`\upsilon_{\omega\cdot\omega}`$ is in $`\mathrm{Core}(R_2^C)`$. Proof: by the cap of
  Theorem EQB, no $`\alpha \lt \upsilon_{\omega\cdot\omega}`$ is $`\le_1`$ to everything above it; by Carlson 2009,
  Thm 14.14, the core is the least such ordinal (or all of Ord).
- **Lemma RESTR.** Below $`\Omega_\omega`$, the hull of InaccPsi and the hull of Pohlers's system with one
  inaccessible (Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof
  Theory 1998, Def 3.4.4.1) agree, and so do their $`\psi_{\Omega_{n+1}}`$. With the cited ordinals of
  $`\mathrm{ID}_{\lt\omega}`$ (Wilken 2021, §1; Pohlers 1998, Fig. 1) this gives
  $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ (cited, indirect). Two weak links are in the literature: Pohlers
  takes regular cardinals for recursively regular ordinals without proof, and Wilken states the ordinal
  of $`\mathrm{ID}_{\lt\omega}`$ without proof.
- $`\psi_{\Omega_1}(0) = \Gamma_0`$, and $`\vartheta_0(\varepsilon_{\Omega+1}) = \psi_{\Omega_1}(\varepsilon_{\Omega_1+1})`$ (cited + RESTR).
- **Theorem MAIN.** These are equivalent: (i) every ordinal of $`\mathrm{Core}(R_2^C)`$ below
  $`\upsilon_{\omega\cdot\omega}`$ is the value of a countable InaccPsi term; (ii) every ordinal below
  $`\upsilon_{\omega\cdot\omega}`$ is; (iii) **Conjecture U**: $`\upsilon_{\omega\cdot\omega} \le D`$, where
  $`D = \sup_a \psi_{\Omega_1}(a)`$. Proof: CORE-C and Lemma IS.
- **Theorem CC** (in $`R_2^C`$). Let $`C^*_n`$ be the pointwise least set of $`n`$ additive principal numbers
  that are pairwise $`\le_2`$. Then $`\mathrm{Core}(R_2^C) = \sup_n \max C^*_n`$, and a pattern with $`n`$ additive
  principal numbers has its least realization below $`\max C^*_{n+1}`$. So in $`R_2^C`$ the claim is a
  statement about least $`\le_2`$-chains. (For Wilken's $`R_2^S`$ this does not follow yet.)
- Small lemmas: **PRINC** ($`x \lt_1 y`$ gives $`x`$ additive principal; $`x \lt_2 y`$ gives $`y`$ additive
  principal), **ISO-UNION** (a finite union of isominimal sets is isominimal), **HULL** (every regular
  uncountable $`\kappa`$ is $`\le_1`$ to everything above it, in both structures), **CORE-S** (the same core
  result for $`R_2^S`$, given two open leaves), **DOM₁** (a pattern without $`\lt_2`$-pairs has its least
  realization below $`\upsilon_1`$).
- $`C^*_2 = \{\upsilon_\omega, \upsilon_{\omega+1}\}`$, and $`\min C^*_3 \ge \upsilon_{\omega^3}`$ given Lemma FRAG of
  [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md) (accepted there only as a sketch).

**Not proved:**

- **The claim below $`\upsilon_{\omega\cdot\omega}`$.** Blocked by Conjecture U. Proved only below $`\upsilon_1`$ (cited
  $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ and Lemma IS).
- By the limit step (Lemma CONT), Conjecture U follows from the successor step: if
  $`\upsilon_\xi = \psi_{\Omega_1}(A)`$, then $`\upsilon_{\xi+1} \le \psi_{\Omega_1}(A + \theta)`$. Every route found
  needs an embedding of Wilken's $`\vartheta`$-terms into an InaccPsi hull. Weiermann–Wilken 2011, p. 117,
  leaves such a translation to future research.
- $`\mathrm{Core}(R_2^S)`$ below $`\upsilon_{\omega\cdot\omega}`$: only the points of the patterns of Theorem S
  ([R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md)) are known to be in it.
- The referee of the route found one blocking gap: the reduction to chains (Theorem CC) and all
  certificates are about $`R_2^C`$, while Wilken's claim is about $`R_2^S`$. The transfer needs
  $`R_2^S = R_2^C`$, which is open.

## 4. Names of Wilken's points (Conjecture T)

**Conjecture T.** With $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$, for $`\eta \le \omega^2`$:

```math
\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta).
```

| $`\eta`$ | point | term |
|---|---|---|
| $`0`$ | $`\upsilon_1`$ | $`\psi_{\Omega_1}(\Omega_\omega)`$ (cited) |
| $`1`$ | $`\upsilon_2`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta)`$ |
| $`2`$ | $`\upsilon_3`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot 2)`$ |
| $`\omega`$ | $`\upsilon_\omega`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1})`$ |
| $`\omega+1`$ | $`\upsilon_{\omega+1}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1} + \theta)`$ |
| $`\omega\cdot 2`$ | $`\upsilon_{\omega\cdot 2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1}\cdot 2)`$ |
| $`\omega^2`$ | $`\upsilon_{\omega^2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+2})`$ |

Only $`\psi_{\Omega_1}`$, $`\psi_{\Omega_2}`$ and $`\Omega_\omega`$ occur: no inaccessible is needed below
$`\upsilon_{\omega\cdot\omega}`$. The naive guess $`\upsilon_\iota = \psi_{\Omega_1}(\Omega_\omega\cdot\iota)`$ is too large from
$`\iota = 2`$ on if Conjecture T holds (Lean: $`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$). Reason for
$`+\theta`$: in Wilken's $`T^\tau`$ the $`\Omega_1`$-level part has the same supremum
$`\vartheta_1`$ for every base $`\tau`$, and $`\theta`$ plays that role in InaccPsi (heuristic). Evidence: the
translation `por/tr3.py` of [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md) gives these points for the
matrices of Theorem S (checked). Conjecture T implies Conjecture U.

## 5. The route: a tree of lemmas

Three routes: B gives the upper bound, A is a full analysis, L gives the lower bound. Below,
"chain of length $`n`$" means $`n`$ additive principal numbers that are pairwise $`\le_2`$.

- **W** Wilken's claim, $`\mathrm{Core}(R_2^+) = \psi_{\Omega_1}(I_\omega)`$ — open
  - **Low** below $`\upsilon_{\omega\cdot\omega}`$
    - Conjecture U, via the successor step $`\upsilon_{\xi+1} \le \psi_{\Omega_1}(A + \theta)`$ — open
      (needs a $`\vartheta \to \psi`$ embedding; start from the simultaneous $`\bar\vartheta`$ of Weiermann–Wilken 2011)
    - Conjecture T (the names of §4) — conjecture
    - $`\mathrm{Core}(R_2^S)`$ contains all of $`\upsilon_{\omega\cdot\omega}`$ — open (needs, for $`R_2^S`$, Carlson 2009,
      Thm 14.10: a minimal copy is the least copy)
  - **B** upper bound $`\mathrm{Core}(R_2^+) \subseteq \psi_{\Omega_1}(I_\omega)`$ — open
    - B0 reduction to least chains (Theorem CC) — proved for $`R_2^C`$
      - B0-S the same for $`R_2^S`$ — open
        - every $`R_2^S`$-relation is an $`R_2^C`$-relation (from Wilken 2021, Lemma 1.7, and the leading-term
          replacement of Theorem EQ) — open, medium
        - coverings give isomorphic copies, or "the isominimal realization is pointwise below every closed
          covering" in $`R_2^S`$ — open, hard
    - B1 explicit chains of every length $`n`$ below $`\psi_{\Omega_1}(I_\omega)`$ as InaccPsi values — open,
      research (no candidate for $`n = 3`$)
    - B2 a finite-set criterion for $`\lt_2`$ (Wilken 2021, Prop 1.6, is for pure $`R_2`$; the transfer to $`+`$
      is not checked) — open, easy
    - B3 base changes that keep $`0, +, \le, \le_1, \le_2`$ (Lemma FRAG extended to $`\le_2`$), proved together with
      B4 — open, very hard
    - B4 the $`\le_2`$-pairs among the points that B3 moves — open, very hard
    - B5 assembly B2 + B3 + B4 — proof form only
    - B-PT proof-theoretic variant: theories with $`n`$ inaccessibles prove "a chain of length $`n`$ exists" —
      open; needs a set-theoretic condition for $`\lt_2`$ that is not known
  - **A** full analysis — open
    - A1 hull systems over every base, with simultaneous collapsing functions for all $`\Omega_\xi`$ and $`I_n`$,
      compared with InaccPsi — open, high
    - A2 a structure theorem for $`\le_1`$, $`\le_2`$ of $`R_2^+`$ up to the bound (the analogue of Wilken 2021,
      Thm 4.2); the results of [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md) are this theorem below
      $`\upsilon_{\omega^3}`$ — open, very hard
    - A3 least realizations as terms — open
    - A4 **Conjecture CH**: the least chain of length $`k+2`$ needs $`k`$ inaccessibles — conjecture
    - A5 every term below the bound is the value of a pattern — open
    - A6 $`R_2^S = R_2^C`$ everywhere — open
  - **L** lower bound $`\psi_{\Omega_1}(I_\omega) \subseteq \mathrm{Core}(R_2^+)`$ — open
    - L0 in $`R_2^C`$: equivalent to "every $`\gamma \lt \psi_{\Omega_1}(I_\omega)`$ is below some $`\max C^*_n`$" — proved
    - L-CERT an order embedding of InaccPsi terms into patterns, each step certified by Carlson's
      rules (no values of $`R_2^+`$ needed); first for terms below $`\psi_{\Omega_1}(I_0)`$ — open, the most feasible
    - L-BMS through $`\Phi_3`$ — blocked: the tested $`\Phi_3`$ patterns have only chains of length 2 (§6)
  - **Side leaves**
    - **DOM₂**: a pattern without a chain of length 3 lies below $`\min C^*_3`$ — checked on 8 certificates
    - locate $`C^*_3`$ — open (known: $`\min C^*_3 \ge \upsilon_{\omega^3}`$ given FRAG)
    - Lean: the order type of the bounded terms is $`\psi_{\Omega_1}(X)`$; Lemma LOC (whether a finite set is
      isominimal depends only on the structure up to its largest element; on paper, not refereed) — open

## 6. Experiments

All checked or conjecture; nothing here is a proof. Each run was under 60 seconds.

**Tools.** A Python port of InaccPsi's comparison, `KLt` and `NF` agrees with Lean's `Term.cmp` on 600 of
600 random pairs and with `NF` on 120 of 120 terms. The trio matrices $`M`$ are read by three programs:
`por/tr3.py` (Wilken's $`\upsilon_\iota`$ and $`T^\tau`$ terms), Ytosk's algorithm (2020, trio matrix →
extended Buchholz $`\psi`$, valid below SRO;
[blog post](https://googology.fandom.com/wiki/User_blog:Ytosk/Algorithm_that_changes_BMS_matrices_into_ordinals_up_to_SRO),
run only), and "BMS analyzer Mk. II" (run only). The pattern of $`M`$ is $`\Phi_3(M)`$ of
`por/phi3def2.py`, and "$`\lt`$" between patterns is shown by certificates of Carlson's rules.

**Table** (the conjectured term $`J`$ of the least realization of $`\Phi_3(M)`$). In the table, `p0(a)` is
$`\psi_{\Omega_1}(a)`$, `p1(a)` is $`\psi_{\Omega_2}(a)`$, `pI0(a)` is $`\psi_{I_0}(a)`$, `W` is $`\Omega_1`$, `W_a` is
$`\Omega_a`$, `w` is $`\omega`$, `w^x` is $`\omega^x`$, `P` is `p1(W_w)`, and `t6` is the term of row 6.
Matrices: `Z` = (0,0,0)(1,1,1), `K` = (1,1,0)(2,2,1). Value status: "proved" = Theorem S below
$`V`$; "FRAG" = Theorem S below $`V_3`$ given FRAG; "num" = checked numerically only. Agrees: which
readings convert to the same $`J`$.

| # | name | M | J | value | agrees |
|---|---|---|---|---|---|
| 1 | υ₁ | `Z` | `p0(W_w)` | cited | tr3, Ytosk |
| 2 | υ₂ | `Z K` | `p0(W_w+P)` | proved | tr3, Ytosk |
| 3 | υ_ω | `Z K (2,0,0)` | `p0(W_w+w^(P+1))` | proved | tr3, Ytosk |
| 4 | U = υ_{ω+1} | `Z K (2,0,0) K` | `p0(W_w+w^(P+1)+P)` | proved | tr3, Ytosk |
| 5 | V₂ = υ_{ω·2+1} | `Z K (2,0,0) K (2,0,0) K` | `p0(W_w+w^(P+1)·2+P)` | proved | tr3, Ytosk |
| 6 | V = υ_{ω²} | `Z K (2,0,0)(2,0,0)` | `p0(W_w+w^(P+2))` | FRAG | tr3, Ytosk |
| 7 | V+1 | `V (1,0,0)` | `w^(t6+1)` | FRAG | tr3 |
| 8 | ε after V | `V (1,1,0)` | `phi(1,t6+1)` | FRAG | tr3 |
| 9 | φ₂ after V | `V (1,1,0)(2,1,0)` | `phi(2,t6+1)` | FRAG | tr3 |
| 10 | BHO after V | `V (1,1,0)(2,2,0)` | `p0(W_w+w^(P+2)+phi(1,W+1))` | FRAG | tr3 |
| 11 | υ_{ω²+1} | `Z K (2,0,0)(2,0,0) K` | `p0(W_w+w^(P+2)+P)` | FRAG | tr3, Ytosk |
| 12 | υ_{ω²+ω} | `Z K (2,0,0)(2,0,0) K (2,0,0)` | `p0(W_w+w^(P+2)+w^(P+1))` | FRAG | tr3, Ytosk |
| 13 | υ_{ω²+ω+1} | `Z K (2,0,0)(2,0,0) K (2,0,0) K` | `p0(W_w+w^(P+2)+w^(P+1)+P)` | FRAG | tr3, Ytosk |
| 14 | υ_{ω²·2} | `Z K (2,0,0)(2,0,0) K (2,0,0)(2,0,0)` | `p0(W_w+w^(P+2)·2)` | FRAG | tr3, Ytosk |
| 15 | V₃ = υ_{ω³} | `Z K (2,0,0)(2,0,0)(2,0,0)` | `p0(W_w+w^(P+3))` | num | tr3, Ytosk |
| 16 | υ_{ω³+1} | `V₃ K` | `p0(W_w+w^(P+3)+P)` | num | tr3, Ytosk |
| 17 | υ_{ω⁴} | `Z K (2,0,0)(2,0,0)(2,0,0)(2,0,0)` | `p0(W_w+w^(P+4))` | num | tr3, Ytosk |
| 18 | υ_{ω^ω} | `Z K (2,0,0)(3,0,0)` | `p0(W_w+w^(P+w))` | num | tr3, Ytosk |
| 19 | BHO after row 18 | `Z K (2,0,0)(3,0,0)(1,1,0)(2,2,0)` | `p0(W_w+w^(P+w)+phi(1,W+1))` | num | tr3 |
| 20 | υ_{ω^ω+1} | `Z K (2,0,0)(3,0,0) K` | `p0(W_w+w^(P+w)+P)` | num | tr3, Ytosk |
| 21 | υ_{ω^ω^ω} | `Z K (2,0,0)(3,0,0)(4,0,0)` | `p0(W_w+w^(P+w^w))` | num | tr3, Ytosk |
| 22 | υ_{ε₀} | `Z K (2,0,0)(3,1,0)` | `p0(W_w+w^(P+eps0))` | num | tr3, Ytosk |
| 23 | υ_{ε₀+1} | `Z K (2,0,0)(3,1,0) K` | `p0(W_w+w^(P+eps0)+P)` | num | tr3, Ytosk |
| 24 | υ at BHO | `Z K (2,0,0)(3,1,0)(4,2,0)` | `p0(W_w+w^(P+p0(phi(1,W+1))))` | num | tr3, Ytosk |
| 25 | υ at υ₁ | `Z K (2,0,0)(3,1,1)` | `p0(W_w+w^(P+p0(W_w)))` | num | tr3, Ytosk |
| 26 | first fixed point of υ | `Z K (2,1,0)` | `p0(W_w+w^(P+W))` | num | Ytosk |
| 27 | | `Z (1,1,1)` | `p0(W_w·2)` | num | Ytosk |
| 28 | | `Z (2,0,0)` | `p0(w^(W_w+1))` | num | Ytosk |
| 29 | | `Z (2,1,0)` | `p0(w^(W_w+W))` | num | Ytosk |
| 30 | | `Z (2,1,0)(3,2,0)` | `p0(phi(1,W_w+1))` | num | Ytosk |
| 31 | | `Z (2,1,0)(3,2,1)` | `p0(W_(w·2))` | num | Ytosk |
| 32 | | `Z (2,1,1)` | `p0(W_(w^2))` | num | Ytosk |
| 33 | | `Z (2,1,1)(3,0,0)` | `p0(W_(w^w))` | num | Ytosk |
| 34 | | `Z (2,1,1)(3,1,0)` | `p0(W_W)` | num | Ytosk |
| 35 | | `Z (2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)` | `p0(W_(W_W))` | num | Ytosk |
| 36 | SRO | `Z (2,1,1)(3,1,0)(2,0,0)` | `p0(pI0(0))` | num | none |

Here BHO is the Bachmann–Howard ordinal, and `phi(1,W+1)` is $`\varepsilon_{\Omega_1+1}`$.

Checked on this table:

- all 36 terms $`J`$ are normal forms and strictly increasing, in Python and in Lean;
- 67 of 67 certificates were found and replayed: $`\Phi_3`$ of row $`i`$ is below $`\Phi_3`$ of row $`i+1`$ for all 35
  neighbour pairs; $`\Phi_3(M[2]) \lt \Phi_3(M)`$ for the 31 rows from $`V`$ on ($`M[n]`$ is the $`n`$-th term of the
  fundamental sequence); $`\Phi_3(\mathrm{SRO}[1]) \lt \Phi_3(\mathrm{SRO}[2])`$;
- tr3 gives the same $`J`$ on the 25 rows it names, Ytosk on 30 rows; no reading disagrees.

**The first inaccessible.** Enumerating all 1,650,729 normal forms of size at most 9: the least countable
term that contains any $`I`$-symbol is $`\psi_{\Omega_1}(\psi_{I_0}(0))`$, and every countable term without one
is below it (checked). Conjecture: the first pattern that needs $`I_0`$ is $`\Phi_3(\mathrm{SRO})`$, with
$`\mathrm{SRO} = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)`$, and its point is $`\psi_{\Omega_1}(\psi_{I_0}(0))`$. Evidence:
$`\mathrm{SRO}[n]`$ reads as $`\psi_{\Omega_1}`$ of an $`\Omega`$-tower of height $`n+2`$; certificates give
$`\Phi_3(\mathrm{SRO}[n]) \lt \Phi_3(\mathrm{SRO})`$ for $`n = 2, 3`$; $`n = 4`$ timed out. Where $`I_1`$ is first needed is
open.

**Chains against $`\Phi_3`$.** For 14 matrices from $`V_3`$ up to $`(0,0,0)(1,1,1)(2,2,2)(3,3,0)`$, the
pattern $`\Phi_3(M)`$ has $`\le_2`$-chains of length at most 2 (checked). Certificates put the point of
$`\Phi_3(M)`$ below $`\min C^*_3`$ for 8 of them and below $`\max C^*_3`$ for 9. If Conjecture CH holds, an order
preserving $`\Phi_3`$ must use chains of length 3 or more past the first inaccessible; with only chains of length 2 it
cannot reach $`\psi_{\Omega_1}(I_\omega)`$. This consequence is **not proved**: it needs values of the matrices that
are not proved, and it is about $`R_2^C`$ only.

## 7. Files

| file | what it proves |
|---|---|
| [CountSeg.lean](CountSeg.lean) | Lemma L, `bounded_inter_Om1`, `vals_inter_Om1`, `three_bounds` |
| [LowSeg.lean](LowSeg.lean) | Lemma IS and Lemma CONT |
| [LowTerms.lean](LowTerms.lean) | the seven terms $`u(\eta)`$ of §4: normal forms, values, order, and $`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ |

Nothing about $`R_2^+`$ itself is in Lean.

## 8. References

- T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001).
- T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009).
- G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
- G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
- A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined θ-functions", MLQ 57 (2011).
- G. Wilken, "A glimpse of Σ₃-elementarity" (2020).
- G. Wilken, "Pure Σ₂-elementarity beyond the core", APAL 172 (2021).
- W. Buchholz, "A simplified version of local predicativity" (1992).
- W. Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof Theory (1998), Ch. IV.
