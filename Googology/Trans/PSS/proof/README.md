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
  Lean's three standard axioms, `#print axioms mainTheorem_mat` lists only the facts cited from
  the literature, stated as axioms in `../TR/Cited.lean` (about Wilken's $`\vartheta`$),
  `../Main/Cited.lean` (about $`R_1^+`$) and `../Main/Cited2.lean` (Wilken's collapse
  $`\iota_{\tau,\alpha}`$, translation $`t^\alpha_\tau`$, [W07b] Thm 5.3 and Cor 5.9). A referee
  checked each of them against the papers and found all of them correct. One reading is still
  not checked against its source: in `P1_isominimal`, a "1-relativized isominimal" set is read as
  an isominimal set. Carlson–Wilken 2012 §6 takes these terms from Wilken, "Assignment of ordinals
  to patterns of resemblance" (JSL 72, 2007), Defs 1.1–1.2, and the isominimality in their
  Cor 6.3(1) is Thm 4.1 of that paper. That paper was not available.
  - Proved on paper and refereed: at $`\tau = 1`$, every reading that fits Carlson–Wilken 2012's own
    description (closed substructures of $`R_1`$, the identity as parameter assignment, $`\le_1`$
    ignored up to the relativization point) is the same as isominimality. In particular, $`Y`$ is
    0-isominimal in their §3 sense if and only if $`\{0\} \cup Y`$ is isominimal.
  - So the axiom holds under every such reading. The gap: that JSL 72 Def 1.2 is one of these
    readings, and that Cor 6.3(1) rests on JSL 72 Thm 4.1.
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
