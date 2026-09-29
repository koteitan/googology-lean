[← 戻る](POR-ja.md) | [English](R2PLUS.md) | [Japanese](R2PLUS-ja.md)

# 理論：$`\upsilon_{\omega+1}`$ より下の $`R_2^+`$

[POR-ja.md](POR-ja.md) の $`\Phi_3`$ の規則は数値で確かめたものである。このページは、$`R_2^+`$ そのものについての最初の定理で、$`\Phi_3`$ の順序の問いを決めるものを記録する。紙の上で証明し（全文はまだ公開していない。Lean には無い）、独立した査読者が 2 回確かめた。

**2 つの構造。** Carlson, "Patterns of resemblance of order 2"（APAL 158, 2009）は $`\le_1, \le_2`$ を被覆で定義し（Def 5.3、5.4）、ふつうの $`\Sigma_n`$ 初等性による定義と同じであることは「別の場所で示す」と書いている。その証明は文献に見つからなかった。$`\Sigma_n`$ の構造を $`R_2^S`$、Carlson の構造を $`R_2^C`$ と書く。[POR-ja.md](POR-ja.md) で使う証明の探索は $`R_2^C`$ を実装している。階数 1 ではこの問題は無い。Carlson 2001、Wilken 2007、Carlson–Wilken 2012 は同じ $`\Sigma_1`$ の定義の $`R_1^+`$ を使う。

**$`R_2^S`$ での結果。** Wilken の点を $`\upsilon_\iota`$ と書く（$`\upsilon_1 = \psi_0(\Omega_\omega)`$）。
- **補題 L。** $`R_1^+`$ で、$`z_0 \in T^\tau \cap (\tau, \tau^\infty)`$ から始まる $`\lt_1`$ の鎖の元は高々 $`\mathrm{ht}_\tau(z_0) + 2`$ 個である。無限の $`\lt_1`$ の鎖は $`\upsilon`$ の点だけからなり、上限は $`\upsilon_\lambda`$（$`\lambda`$ は極限）である。
- **定理 A。** $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ は最小の $`\lt_2`$ の組である。$`[0, \upsilon_{\omega+1}]`$ の上で $`\le_1`$ は $`R_1^+`$ のものと同じで、ほかの $`\lt_2`$ は無く、$`\mathrm{lh}(\alpha) = \min(\mathrm{lh}_{R_1^+}(\alpha), \upsilon_{\omega+1})`$ である。証明は Wilken, "A glimpse of $`\Sigma_3`$-elementarity"（2020）の Thm 21.13 に沿い、翻訳の代わりに彼の底の取り替え（[W07b] Cor 5.7）を使う。
- **定理 B。** $`\upsilon_{\omega\cdot\omega}`$ より下の $`\lt_2`$ の組はちょうど $`\upsilon_{\omega k} \lt_2 \upsilon_{\omega k+1}`$ で、各 $`\upsilon_{\omega k+1}`$ は閉じており、各ブロックの中で $`R_2^S`$ は $`R_1^+`$ と一致する。
- **命題 P′。** $`\upsilon_{\omega+1}`$ より下の 4 つの形のトリオ行列（最初の検査の組の標準形 538 個のうち 369 個）では、$`\Phi_{3m}(M)`$ の最小の実現は点を $`\mathcal{T}_3(M)`$（`por/tr3.py` の翻訳）に置く。形の仮定はこれらの行列で確かめたもので、全部について証明したものではない。その結果、[POR-ja.md](POR-ja.md) §9 の未決の組のうち 20 組が $`R_2^S`$ で「$`\lt`$」と決まる。

**この範囲では 2 つの構造は一致する（定理 EQ）。** $`R_2^C`$ と $`R_2^S`$ は、$`[0, \upsilon_{\omega+1}]`$ で同じ $`\le_1`$ と $`\le_2`$ を持ち、届く先の上限も同じである。$`\le_1`$ の一方の向きは、$`\Sigma_1`$ で同型なコピーを取り、各値をその先頭の項に置き換える（Carlson 2001 の Lemma 3.2、3.13）。もう一方の向きは、[W07b] Thm 5.3 の証明の中の Claim 5.5(b) を使う。これは Carlson の Def 5.3 の被覆をちょうど排除する。$`\le_2`$ でも、組は $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ だけである。Carlson 2009 の Thm 14.10 と合わせて、命題 P′ と決まった 20 組は、証明の探索が実装している構造 $`R_2^C`$ でも成り立つ。（Carlson の Def 5.3 の節 2 は、彼自身の Lemma 5.5(6)、5.7(3) の証明と同じく「$`X \cup Y`$ が閉じている」と読む。）$`R_2^C`$ での定理 B は見取り図だけである。査読者は定理 EQ に穴を見つけなかった。

**条件つき、または未解決。**
- $`\upsilon_{\omega+1}`$ より下のさらに 10 組（別の 2 つの形）は、Carlson–Wilken 2012 の §7 にある、証明の無い注意書きのもとでだけ決まる（一般の底では、手に入らなかった Wilken, "Assignment of ordinals to patterns of resemblance", JSL 72, 2007 の読み方も要る）。
- $`\upsilon_{\omega+1}`$ より上での $`R_2^C`$ と $`R_2^S`$ の一致（$`R_2^C`$ での定理 B は見取り図だけ）。
- $`\upsilon_{\omega\cdot\omega}`$ より上：各「背骨」は Wilken の $`R_2`$ の $`\varepsilon_0`$ の倍数のようにふるまう、という予想は、試した 11,506 件の事実すべてと一致する。$`\Omega_2`$ の段の構造を持つ頭は扱えず、文献が今後の課題としている算術が要る。

