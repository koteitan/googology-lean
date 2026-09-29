[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# PSS

The translation of pair sequences (Bashicu matrices with two rows) into the
ordinals. It goes through the translation `Trans` of p進大好きbot's article
[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7),
whose bijectivity Naruyoko proved and
[koteitan/pss-proof](https://github.com/koteitan/pss-proof) formalizes. That
repository is a Lake dependency; its theorems are used, not copied.

## Files

| file | contents |
|---|---|
| `Expand.lean` | pss-proof's expansion is this library's: `oper M (N+1) = expand2L N M` on every standard pair sequence of length at least 2 (`oper_succ_eq_expand2L_of_ctps`), and the two notions of standard agree (`isPair_iff`) |
| `Terms.lean` | pss-proof's Buchholz terms, with subscripts in `ℕ ∪ {ω}`, map injectively and order-preservingly into extended Buchholz terms (`toTerm_injective`, `lessBT_iff_lt`), standard exactly when their image is (`OT_toTerm_iff`), onto the standard forms below `ψ_0(Ω_ω)` (`toTerm_bijOn_TransRange`) |
| `Rank.lean` | **the rank of a pair sequence is `1 + val` of its term** (`rank_pairL_eq`), 0 for the empty sequence; the values are exactly the ordinals below `ψ_0(Ω_ω)` (`range_pairOrd`); the map is injective and order-preserving for the lexicographic order (`pairOrd_injective`, `ltPS_iff_pairOrd_lt`); and the rank is the order type of the standard pair sequences below (`rank_eq_typein`) |
| `SC.lean`, `SC/` | **Theorem SC** of [proof/COMB.md](proof/COMB.md) §8b, fully proved (no `sorry`): a pair sequence is standard exactly when it satisfies (R0), (I0), (A), Sib and G\* on its forest of row-0 parents (`ctps_iff_SC`). Part 1, standard ⇒ SC, is `sc_of_ctps` (by induction on expansion, `SC/Step.lean`, `SC/Pert.lean`); Part 2, SC ⇒ standard, is `ctps_of_sc` (`Forest.ctps_of_SC` in `SC/Part2.lean`, via the least standard sequence above). The conditions are in `SC/Defs.lean`, the tree view (parents, terms, the order of terms) in `SC/Basic.lean` and `SC/Tree.lean`. Axioms: `propext`, `Classical.choice`, `Quot.sound` |
| `Phi.lean`, `Phi/` | the term operations of $`\Phi`$ ([POR.md](POR.md) §3: anchor, `log`, `Coll_A`, `lh`), computable and checked against `por/phi.py` on small examples, and their facts from [proof/COMB.md](proof/COMB.md), fully proved (no `sorry`): Theorem SC on terms (`sc_mat_iff`, `ctps_cols_iff`); the anchor, `log` and `lh` of a standard term are standard (Lemma 2.4 and Lemma 6: `ctps_anchor`, `node_log0`, `ctps_lh`), through Lemma C (`std_lemmaC`) and Lemma 10 (`coll_lt_coll`); Theorem T, the fuel of `lh` is enough for every term (`lhF_eq_lh`); Lemma R, $`o(N) = \omega^{o(\mathcal{L}N)}`$ for standard $`N`$ (`lemmaR`, `lemmaR_log`, `lemmaR_eps`), through Lemma 5 (a) (`ordOf_append`) and $`\mathcal{L}`$ strictly monotone and onto the nodes (`bigL_lt_iff`, `exists_bigL_eq`). Axioms: `propext`, `Classical.choice`, `Quot.sound` |
| `TR.lean`, `TR/` | **Lemma TR** of [proof/TR.md](proof/TR.md): the translation $`\mathcal{T}`$ of pair sequences into Wilken's $`T^1`$ (as `por/tr.py`, checked on small examples by `decide`) satisfies $`\mathrm{val} \circ \mathcal{T} = o`$ (`tr`, `tr_mat`), through Theorem M (Mono\*: `mono`, `mono_node`) and Theorem Cof (`cof`), with no `sorry`. The cited facts on Wilken's ϑ-functions ((L), (C), (E), (Exp), (Seg), (Min) of [proof/TR.md](proof/TR.md) §1) are the axioms of `TR/Cited.lean`; (Min) is not used. Axioms: `propext`, `Classical.choice`, `Quot.sound` and those of `TR/Cited.lean` |
| `Main.lean`, `Main/` | **the Main Theorem** of [proof/PROOF.md](proof/PROOF.md): $`\iota(\Phi(M)) = o(M) = 1 + \mathrm{val}(\mathrm{pairTerm}\ M)`$ for every standard pair sequence (`mainTheorem`, `mainTheorem_mat`), and Cor 7.2: $`\iota \circ \Phi`$ keeps the order (`cor72a`) and its image is $`[1, \psi_0(\Omega_\omega))`$ (`cor72b`), which is $`\mathrm{Core}(R_1^+) \setminus \{0\}`$ given the axiom `core_eq_psi` (`cor72b_core`). Proved on the way: Lemma F and Prop 4.3 (`fold_isLh`), the reach lemma L (`lemmaL`), Lemma 5.1, Lemma 6.1, Theorem VF ($`V_M`$ is finite: `thmVF`, `finite_V`), bar-closure (`barClosure`, with $`\mathrm{Bar}_T`$ as `barEps`) and Theorem 11.1 (`thm111`). The cited facts on $`\le_1`$ and $`R_1^+`$ ([W07b] Lemma 2.1, Thm 2.2, Lemmas 3.3, 3.4, Cor 5.10; [CW12] Core Structure Theorem (2), Cor 6.3) are the axioms of `Main/Cited.lean`. E1 and E2 (`Main/E12.lean`) are proved through Wilken's maps $`\iota_{1,\alpha}`$ and $`t^\alpha_\tau`$ with Lemma CI (`ci`), $`\mathrm{E1}_T`$ (`e1T`) and PL (`pl`); the cited [W07a] Def 6.2, 7.1, 7.5, Cor 7.3, Lemma 6.3 and [W07b] Thm 5.3, Cor 5.9 are the axioms of `Main/Cited2.lean`. No `sorry`. Axioms: `propext`, `Classical.choice`, `Quot.sound`, and those of `TR/Cited.lean`, `Main/Cited.lean` and `Main/Cited2.lean` |

## A map to additive patterns

[POR.md](POR.md) defines a map $`\Phi`$ from standard pair sequences to Carlson's additive patterns $`R_1^+`$, by rearranging the trees of the matrix. $`\Phi`$ preserves the lexicographic order and its image is the whole core of $`R_1^+`$ except 0: this is proved on paper in [proof/](proof/README.md), with numerical evidence (144,773 adjacent pairs and 7,471,992 random pairs, 0 violations). The map and the translation are programs in Python (`por/phi.py`, `por/pss.py`, `por/tr.py`). In Lean, all three parts of the proof are formalized. (1) The pair-sequence part: Theorem SC (`SC.lean`) and the term operations with Lemma C, Lemma 2.4, Theorem T and Lemma R (`Phi.lean`). (2) Lemma TR, the translation to Wilken's $`\vartheta`$ with $`\mathrm{val} \circ \mathcal{T} = o`$ (`TR.lean`); the cited facts about $`\vartheta`$ are axioms collected in `TR/Cited.lean`. (3) The main chain up to $`\iota(\Phi(M)) = o(M)`$ and Cor 7.2 (`Main.lean`); the cited facts about $`R_1^+`$ are axioms collected in `Main/Cited.lean`. The main chain has no `sorry`; the cited facts of Wilken's E1 and E2 are axioms collected in `Main/Cited2.lean`.

## Why `1 +`

The pair sequence system of this library runs one step further than
pss-proof's: pss-proof stops at `(0,0)`, and this library expands `(0,0)` to
the empty sequence. So every nonempty sequence has one more state below it,
and its rank is `1 + val (Trans M)`. For an infinite value `1 + α = α`, so the
generator `(0,0)(1,1)` still has rank `ε₀`.

## Route

1. `Expand.lean` puts the two expansion systems side by side.
2. pss-proof's `trans_bijOn` and `trans_order_iso` make `Trans` an order
   isomorphism from the standard pair sequences onto the standard Buchholz
   terms below `D_0 D_ω 0`.
3. `Terms.lean` carries that onto the standard extended Buchholz terms below
   `ψ_0(Ω_ω)`.
4. `belowEquiv` (in `Notation/ExBuchholz/Onto.lean`) says the standard forms
   below a countable standard form `X` are, in order, the ordinals below
   `val X`. So the order type below a pair sequence is the value of its term.
5. Expansion is cofinal among the standard pair sequences below (from
   pss-proof's `ltPS_ltExpPS` and `expand_lePS`), so the rank is that order type.
