[← Back](../POR.md) | [English](README.md) | [Japanese](README-ja.md)

# A proof for the map $`\Phi`$ from pair sequences to $`R_1^+`$-patterns

This directory contains a proof on paper for the map $`\Phi`$ of [POR.md](../POR.md). $`\Phi`$
sends a standard pair sequence $`M`$ to an additive pattern of resemblance of order 1,
$`\Phi(M)`$, in the sense of Carlson.

## The theorem

**Main Theorem.** For every standard pair sequence $`M`$:

```math
\iota(\Phi(M)) = o(M) = 1 + \mathrm{val}(\mathrm{pairTerm}(M))
```

- $`\iota(P)`$ is the value of the point of the pattern $`P`$ in its isominimal realization.
- $`o(M)`$ is `pairOrdL M`, the ordinal of $`M`$ in [Rank.lean](../Rank.lean).
- `pairTerm` is the map of [Rank.lean](../Rank.lean) from pair sequences to Buchholz's
  $`\psi`$-terms.

Two consequences ([PROOF](PROOF.md) Cor 7.2):

- (a) $`\Phi`$ keeps the order: $`M \lt_{\mathrm{lex}} M' \iff \iota(\Phi(M)) \lt \iota(\Phi(M'))`$.
  This is the conjecture of [POR.md](../POR.md).
- (b) The values $`\iota(\Phi(M))`$ are exactly the ordinals in
  $`[1, \psi_0(\Omega_\omega))`$, that is, $`\mathrm{Core}(R_1^+) \setminus \{0\}`$.

## Status

- Proved on paper. Each of the three parts was checked by an independent referee, who tried
  to refute it. No referee found a false statement. Every gap and every minor point the
  referees found has been repaired; the repairs of PROOF and TR were checked again by the
  same referees. The repairs of COMB were minor (citations and omitted one-line steps) and
  were not re-checked.
- **In Lean, with no `sorry`.** The whole proof is formalized: Theorem SC (`../SC.lean`), the
  term operations and Lemmas C, 2.4, T, R (`../Phi.lean`), Lemma TR (`../TR.lean`), and the main
  chain with E1, E2, the Main Theorem `mainTheorem_mat` and Cor 7.2 (`../Main.lean`). Besides
  Lean's three standard axioms, `#print axioms mainTheorem_mat` lists only 42 facts cited from
  the literature, stated as axioms in `../TR/Cited.lean` (about Wilken's $`\vartheta`$),
  `../Main/Cited.lean` (about $`R_1^+`$), `../Main/Cited2.lean` (Wilken's collapse
  $`\iota_{\tau,\alpha}`$, translation $`t^\alpha_\tau`$, [W07b] Thm 5.3 and Cor 5.9) and `../Main/Cited3.lean`
  (the inverse base change $`\pi^{-1}`$ of [W07a] Def 5.1, [W07a] Lemma 5.3, Cor 5.4 and [W07b]
  Cor 5.7, 5.10; the epsilon case of [CW12] Lemma 5.7.1; [W07a] Thm 3.23 and Lemma 3.27; [W07b]
  Lemma 4.5). A referee checked each of them against the papers and found all of them correct.
  Every axiom takes its hypotheses as explicit arguments (no `variable` line).
  - The axioms `P1_isominimal`, `exists_isominimal` and `pwLe_of_covering` are removed, together
    with `thm111` and `lemma61`. So the Main Theorem does not use Wilken, "Assignment of ordinals to
    patterns of resemblance" (JSL 72, 2007), which was not available, nor the Core Structure
    Theorem and Cor 6.3 of Carlson–Wilken 2012. They are replaced by three theorems, proved on
    paper, refereed, and now proved in Lean:
    - **Theorem S+ at base $`\sigma \ge 1`$** (`splus`, `../Main/SPlus.lean`). The proof of Theorem S+ of
      [../../BMS/R2PLUS.md](../../BMS/R2PLUS.md) works for every base $`\sigma \ge 1`$. In Lean it
      uses an absorption law ($`x + q = q`$ implies $`h(x) \cdot \omega \le h(q)`$) in place of "principal
      numbers go to principal numbers".
    - **Theorem FIN** (`finite_inC`, `finite_P1`, `../Main/Fin.lean`). $`P_1(\alpha)`$ is finite for
      $`1 \lt \alpha \lt \psi_0(\Omega_\omega)`$, by induction on $`(\mathrm{ht}_\sigma(y), y)`$ in lexicographic order.
    - **Theorem LEAST** (`ordV_least`, `iotaPat_eq_least`, `../Main/Least.lean`). Every isomorphism
      $`g`$ of $`X = o[V_M]`$ onto any set satisfies $`g \ge \mathrm{id}`$. So $`X`$ is isominimal, and
      $`\iota(\Phi(M)) = o(M)`$.
  - Checks: the library builds (9,242 jobs) with no "declaration uses sorry"; the list of
    `#print axioms mainTheorem_mat` has no `sorryAx` and none of the removed axioms. The statements of
    `mainTheorem_mat`, `mainTheorem` and Cor 7.2 are the same as before. The referee looked for a
    contradiction among the new axioms (for example at $`\gamma = 0`$, $`\alpha = 1`$) and found none.
    [CW12] Lemma 5.7.1 has a known error in its other (non-epsilon) case, which is not used. In the
    epsilon case, the direction that the axiom `lemma571_eps` states is also proved on paper; the
    other direction is only cited.
- **One outside assumption.** The Lean function `Ord.psi`
  ([Ord.lean](../../../Notation/ExBuchholz/Ord.lean)) is Buchholz's $`\psi`$. This is used only
  to read Cor 7.2(b) as "the image is $`\mathrm{Core} \setminus \{0\}`$": [Rank.lean](../Rank.lean)
  gives the range of $`o`$ as the ordinals below `Ord.psi (Ord.Omega ω) 0`, and the literature
  identifies the core with Buchholz's $`\psi_0(\Omega_\omega)`$. The Main Theorem and Cor 7.2(a)
  do not use this assumption.

## Structure of the proof

The proof has three parts. Each part uses only the parts before it:

```math
\text{COMB} \to \text{TR} \to \text{PROOF}
```

| document | what it proves |
|---|---|
| [COMB.md](COMB.md) | Lemmas on pair sequences. Theorem SC: a matrix is standard if and only if its row-0 tree satisfies local conditions. S1: a matrix is standard if and only if its root segments are standard and do not increase. Lemma R: $`o(N) = \omega^{o(\mathcal{L} N)}`$ for one-root $`N`$. Lemma C and Lemma 2.4: the anchors, the reaches $`\mathrm{lh}_\Phi`$ and the fold inputs are standard. T: the recursion of $`\mathrm{lh}_\Phi`$ terminates. |
| [TR.md](TR.md), [TR-2.md](TR-2.md) | Lemma TR: the translation $`\mathcal{T}`$ of pair sequences into Wilken's $`\vartheta`$-terms is correct, $`\mathrm{val} \circ \mathcal{T} = o`$. The proof has two steps: Mono\* ($`\mathcal{T}`$ is strictly increasing at every level) and Theorem Cof ($`\sup_n \mathcal{T}(M[n]) = \mathcal{T}(M)`$ for every limit $`M`$). |
| [PROOF.md](PROOF.md), [PROOF-2.md](PROOF-2.md), [PROOF-3.md](PROOF-3.md), [PROOF-4.md](PROOF-4.md) | The main proof. The reach lemma L ($`\mathrm{lh}(o(N)) = o(\mathrm{lh}_\Phi N)`$), the finiteness of the universe $`V_M`$ of $`\Phi(M)`$ (Thm VF), the embedding of $`\Phi(M)`$ into $`R_1^+`$ (Lemma 5.1), the closure under Wilken's bar operator, and the Main Theorem through Carlson and Wilken's [CW12] Thm 6.2 (Thm 11.1, Thm 7.1, Cor 7.2). |

PROOF and TR are split into several files, because GitHub renders only a limited amount of
math on one page. Sections and lemmas are numbered through the files of each document.

§0 of [PROOF.md](PROOF.md) lists the steps of the main chain with the lemmas each step uses.
The last file of each document ([COMB.md](COMB.md), [TR-2.md](TR-2.md),
[PROOF-4.md](PROOF-4.md)) ends with a "Review history" section: what the referee found, and
where it was repaired.

## Programs

- [../por/phi.py](../por/phi.py): the map $`\Phi`$.
- [../por/pss.py](../por/pss.py): matrices, terms, the order and the expansion of pair
  sequences.
- [../por/tr.py](../por/tr.py): the translation $`\mathcal{T}`$ ([PROOF](PROOF-2.md) §12.1),
  and Wilken's $`\lambda`$, $`\mathrm{lh}^1`$ and bar operator on $`T^1`$-terms.
  `python3 por/tr.py "(0,0)(1,1)(2,2)"` prints $`\mathcal{T}(M)`$.
- The numerical checks reported in the documents were made with further scripts that are
  not published. Some of them used Samuel Alexander's calculator
  [poral](https://github.com/semitrivial/poral) as an oracle. poral has no license, so no
  part of it is included here.

## An erratum in the literature

While formalizing, we found that Lemma 5.7.1 of Carlson and Wilken, "Normal forms for
elementary patterns" (JSL 77, 2012), disagrees with their own Definition 5.1 of the bar
operator. Take $`\alpha = \omega^{\omega^{\varepsilon_0+1}} = \vartheta(\vartheta(\vartheta(\Omega_1)))`$ and
$`\tau = 1`$; its localization is $`(1, \varepsilon_0, \alpha)`$.
- Definition 5.1 gives $`\bar{\alpha} = \varepsilon_0`$ (here $`\eta' = 0`$ and $`\eta_0 = \omega^{\varepsilon_0+1} \ne 1`$,
  so $`\bar{\alpha} = \alpha_{n-1}`$).
- Lemma 5.7.1, non-epsilon case, gives $`\bar{\alpha} = \max(\{\gamma \in (\tau,\alpha) \cap P : \lambda_\gamma \ge \lambda_\alpha\} \cup \{\tau\}) = 1`$,
  because $`\lambda_\alpha = \varepsilon_0 + 1`$ and every principal $`\gamma \lt \alpha`$ has $`\lambda_\gamma \le \varepsilon_0`$.

The lemma repeats the statement of Wilken's "Ordinal arithmetic based on Skolem hulling" (APAL
145, 2007), Lemma 8.2, whose proof sets $`\bar{\alpha} = \alpha_{n-1}`$ without checking
$`\lambda_{\alpha_{n-1}} \ge \lambda_\alpha`$. Definition 5.1 agrees with that proof, and the rest of the
2012 paper (Lemma 5.10(3), Theorem 6.1) follows Definition 5.1. The proof here uses Definition
5.1 and never cites Lemma 5.7.1; Corollary 6.3, which it does use, is not affected. The epsilon
case of Lemma 5.7.1 agrees with Definition 5.1.

## Sources

Literature:

- [C01] T. J. Carlson, "Elementary patterns of resemblance", Annals of Pure and Applied Logic
  108 (2001) 19–77. doi:10.1016/S0168-0072(00)00040-3.
- [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", Annals of Pure and Applied
  Logic 145 (2007) 130–161. doi:10.1016/j.apal.2006.07.003.
- [W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", Annals of Pure and Applied
  Logic 145 (2007) 162–175. doi:10.1016/j.apal.2006.07.004.
- [WW11] A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined
  theta-functions", Mathematical Logic Quarterly 57 (2011) 116–132.
  doi:10.1002/malq.200910125.
- [CW12] T. J. Carlson, G. Wilken, "Normal forms for elementary patterns", Journal of
  Symbolic Logic 77 (2012) 174–194. doi:10.2178/jsl/1327068698.
- [W24] G. Wilken, "Fundamental sequences based on localization", arXiv:2410.15953.
- [A15] S. A. Alexander, "Arithmetical algorithms for elementary patterns", Archive for
  Mathematical Logic 54 (2015) 113–132. doi:10.1007/s00153-014-0404-9.
- [B86] W. Buchholz, "A new system of proof-theoretic ordinal functions", Annals of Pure and
  Applied Logic 32 (1986) 195–207. doi:10.1016/0168-0072(86)90052-7.
- Further works cited in [PROOF-4.md](PROOF-4.md#references): [C09], [W06], [W07c], [W21], [F21].

Lean:

- [pss-proof](https://github.com/koteitan/pss-proof): the facts on standard pair sequences,
  their expansion, and the map `Trans` to Buchholz terms.
- This library: [Rank.lean](../Rank.lean) (the ordinal $`o`$ and its range) and
  [Expand.lean](../Expand.lean) (the expansion of pair sequences).
