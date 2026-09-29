[← 戻る](../POR-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# ペア数列から $`R_1^+`$ パターンへの写像 $`\Phi`$ の証明

このディレクトリには、[POR-ja.md](../POR-ja.md) の写像 $`\Phi`$ についての紙の上の証明がある。
$`\Phi`$ は標準形のペア数列 $`M`$ を、Carlson の意味の 1 階の加法的パターン $`\Phi(M)`$ に送る。

証明の本文（PROOF、COMB、TR）は英語だけである。

## 定理

**主定理。** 標準形のペア数列 $`M`$ すべてについて:

```math
\iota(\Phi(M)) = o(M) = 1 + \mathrm{val}(\mathrm{pairTerm}(M))
```

- $`\iota(P)`$ は、パターン $`P`$ を isominimal に実現したときの、$`P`$ の点の値。
- $`o(M)`$ は [Rank.lean](../Rank.lean) の `pairOrdL M`。$`M`$ の順序数である。
- `pairTerm` は [Rank.lean](../Rank.lean) の写像。ペア数列を Buchholz の $`\psi`$ 項に送る。

ここから 2 つのことが出る（[PROOF](PROOF.md) Cor 7.2）:

- (a) $`\Phi`$ は順序を保つ: $`M \lt_{\mathrm{lex}} M' \iff \iota(\Phi(M)) \lt \iota(\Phi(M'))`$。
  これが [POR-ja.md](../POR-ja.md) の予想である。
- (b) 値 $`\iota(\Phi(M))`$ の全体は、ちょうど $`[1, \psi_0(\Omega_\omega))`$ の順序数である。
  つまり $`\mathrm{Core}(R_1^+) \setminus \{0\}`$ である。

## 状態

- 紙の上で証明した。3 つの部分それぞれを、独立した査読者が、反証するつもりで確かめた。偽の命題は見つからなかった。査読者が見つけた穴と細かい点は、すべて直した。PROOF と TR の直しは、同じ査読者がもう一度確かめた。COMB の直しは細かいもの（引用と、省いていた 1 行の手順）で、もう一度は確かめていない。
- **Lean。** 鎖の全体を形式化した。定理 SC（`../SC.lean`）、項の操作と補題 C・2.4・T・R（`../Phi.lean`）、Lemma TR（`../TR.lean`）、主な鎖と主定理 `mainTheorem_mat`・Cor 7.2（`../Main.lean`）である。ただし E1 と E2 の 2 つの命題は、まだ `../Main/E12.lean` で `sorry` である（作業中）。文献から引用した事実は、`../TR/Cited.lean`（Wilken の $`\vartheta`$ について 11 個）と `../Main/Cited.lean`（$`R_1^+`$ について 20 個）に公理として置いた。査読者がそれぞれを論文と照らし合わせ、すべて正しいと確かめた。
- **外からの仮定が 1 つある。** Lean の関数 `Ord.psi`
  （[Ord.lean](../../../Notation/ExBuchholz/Ord.lean)）が Buchholz の $`\psi`$ であること。
  これを使うのは、Cor 7.2(b) を「像は $`\mathrm{Core} \setminus \{0\}`$」と読むところだけである。
  [Rank.lean](../Rank.lean) は $`o`$ の値域を `Ord.psi (Ord.Omega ω) 0` より下の順序数とする。
  文献は core を Buchholz の $`\psi_0(\Omega_\omega)`$ とする。この 2 つをつなぐのにこの仮定が要る。
  主定理と Cor 7.2(a) はこの仮定を使わない。

## 証明の組み立て

証明は 3 つの部分からなる。どの部分も、それより前の部分だけを使う:

```math
\text{COMB} \to \text{TR} \to \text{PROOF}
```

| 文書 | 証明すること |
|---|---|
| [COMB.md](COMB.md) | ペア数列の補題。Theorem SC: 行列が標準形であることは、行 0 の木が局所的な条件を満たすことと同じ。S1: 行列が標準形であることは、根の区間がどれも標準形で、増えないことと同じ。Lemma R: 根が 1 つの $`N`$ で $`o(N) = \omega^{o(\mathcal{L} N)}`$。Lemma C と Lemma 2.4: anchor、到達点 $`\mathrm{lh}_\Phi`$、畳み込みの入力はどれも標準形。T: $`\mathrm{lh}_\Phi`$ の再帰は止まる。 |
| [TR.md](TR.md), [TR-2.md](TR-2.md) | Lemma TR: ペア数列を Wilken の $`\vartheta`$ 項に移す翻訳 $`\mathcal{T}`$ は正しい。つまり $`\mathrm{val} \circ \mathcal{T} = o`$。証明は 2 段: Mono\*（$`\mathcal{T}`$ はどの階でも狭義に増える）と Theorem Cof（極限の $`M`$ で $`\sup_n \mathcal{T}(M[n]) = \mathcal{T}(M)`$）。 |
| [PROOF.md](PROOF.md), [PROOF-2.md](PROOF-2.md), [PROOF-3.md](PROOF-3.md), [PROOF-4.md](PROOF-4.md) | 本体の証明。到達の補題 L（$`\mathrm{lh}(o(N)) = o(\mathrm{lh}_\Phi N)`$）、$`\Phi(M)`$ の台 $`V_M`$ が有限であること（Thm VF）、$`\Phi(M)`$ の $`R_1^+`$ への埋め込み（Lemma 5.1）、Wilken の bar 演算で閉じていること、そして Carlson と Wilken の [CW12] Thm 6.2 を通した主定理（Thm 11.1、Thm 7.1、Cor 7.2）。 |

PROOF と TR はいくつかのファイルに分けてある。GitHub は 1 ページの数式を一定の量までしか表示しないからである。
節と補題の番号は、1 つの文書の中でファイルをまたいで続いている。

[PROOF.md](PROOF.md) の §0 に、主な道筋の各段と、それぞれが使う補題の表がある。
各文書の最後のファイル（[COMB.md](COMB.md)、[TR-2.md](TR-2.md)、[PROOF-4.md](PROOF-4.md)）の
終わりに「Review history」の節がある。査読者が見つけたことと、それを直した場所を書いてある。

## プログラム

- [../por/phi.py](../por/phi.py): 写像 $`\Phi`$。
- [../por/pss.py](../por/pss.py): 行列、項、順序、ペア数列の展開。
- [../por/tr.py](../por/tr.py): 翻訳 $`\mathcal{T}`$（[PROOF](PROOF-2.md) §12.1）。
  あわせて、$`T^1`$ の項の上の Wilken の $`\lambda`$、$`\mathrm{lh}^1`$、bar 演算。
  `python3 por/tr.py "(0,0)(1,1)(2,2)"` で $`\mathcal{T}(M)`$ を表示する。
- 文書にある数値の確かめには、公開していないスクリプトも使った。その一部は、
  Samuel Alexander の計算機 [poral](https://github.com/semitrivial/poral) を答え合わせに使った。
  poral にはライセンスが無いので、ここには一切含めていない。

## 文献の誤り

形式化の途中で、Carlson と Wilken, "Normal forms for elementary patterns"（JSL 77, 2012）の Lemma 5.7.1 が、同じ論文の bar 操作の定義 Definition 5.1 と食い違うことが分かった。$`\alpha = \omega^{\omega^{\varepsilon_0+1}} = \vartheta(\vartheta(\vartheta(\Omega_1)))`$、$`\tau = 1`$ とする。$`\alpha`$ の localization は $`(1, \varepsilon_0, \alpha)`$ である。
- Definition 5.1 では $`\bar{\alpha} = \varepsilon_0`$ になる（$`\eta' = 0`$、$`\eta_0 = \omega^{\varepsilon_0+1} \ne 1`$ なので $`\bar{\alpha} = \alpha_{n-1}`$）。
- Lemma 5.7.1 の $`\varepsilon`$ 数でない場合の式 $`\bar{\alpha} = \max(\{\gamma \in (\tau,\alpha) \cap P : \lambda_\gamma \ge \lambda_\alpha\} \cup \{\tau\})`$ では 1 になる。$`\lambda_\alpha = \varepsilon_0 + 1`$ で、$`\alpha`$ より小さい主要な $`\gamma`$ はどれも $`\lambda_\gamma \le \varepsilon_0`$ だからである。

この補題は、Wilken, "Ordinal arithmetic based on Skolem hulling"（APAL 145, 2007）の Lemma 8.2 の言明を写したものである。その証明は、$`\lambda_{\alpha_{n-1}} \ge \lambda_\alpha`$ を確かめずに $`\bar{\alpha} = \alpha_{n-1}`$ としている。Definition 5.1 はこの証明と合い、2012 年の論文の残り（Lemma 5.10(3)、Theorem 6.1）も Definition 5.1 に従う。ここでの証明は Definition 5.1 を使い、Lemma 5.7.1 は引用しない。使っている Corollary 6.3 には影響しない。Lemma 5.7.1 の $`\varepsilon`$ 数の場合は Definition 5.1 と一致する。

## 出典

文献:

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
- ほかに [PROOF-4.md](PROOF-4.md#references) で引いている文献: [C09]、[W06]、[W07c]、[W21]、[F21]。

Lean:

- [pss-proof](https://github.com/koteitan/pss-proof): 標準形のペア数列、その展開、Buchholz 項への写像 `Trans` についての事実。
- このライブラリ: [Rank.lean](../Rank.lean)（順序数 $`o`$ とその値域）と
  [Expand.lean](../Expand.lean)（ペア数列の展開）。
