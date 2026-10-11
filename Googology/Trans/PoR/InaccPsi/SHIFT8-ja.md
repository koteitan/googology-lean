[← Back](README-ja.md) | [English](SHIFT8.md) | [Japanese](SHIFT8-ja.md)

# $`R_2^+`$ の 33 回目と 34 回目：定理 B$`^\nu`$、$`L(\varepsilon_{\Phi_\Omega+1})`$ までの点 $`L(e)`$ の骨組み、監査の残り、$`R_2^S`$ での Carlson の範疇性の定理、$`\psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$ までの素の符号

このページは [SHIFT7-ja.md](SHIFT7-ja.md) の続き（そこの §3 が 32 回目）。§1 が 33 回目、§2 が 34 回目。35〜37 回目は [SHIFT9-ja.md](SHIFT9-ja.md)、38〜40 回目は [SHIFT10-ja.md](SHIFT10-ja.md)、41〜43 回目は [SHIFT11-ja.md](SHIFT11-ja.md) にある。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことの言い直しにすぎないと言った結果は、進みとして数えない。

**のちに（40 回目、[SHIFT10-ja.md](SHIFT10-ja.md) §3.2）：** このページの $`\nu_C`$ より上の結果は、$`\nu_C = \nu_S = L(\omega+1)`$（[SHIFT7-ja.md](SHIFT7-ja.md) §2.1）と、長い符号で前のちょうどの長い値を使う区間の中のちょうどの計算（GAP-CALC$`^{\mathrm{reg}}`$）に立つので、**書いたままでは証明されていない**：定理 B$`^\nu`$ と $`L(\omega^2)`$、FRAG″ (d)、FRAG2″、定理 C″ と $`L(\Omega_1\cdot\omega)`$（§1.1）、CAP-SUPPLY (ii) と $`\nu`$ より上の $`R_2^S`$（§1.2）、$`L(\varepsilon_{\Phi_\Omega+1})`$（§2.1）、$`R_2^S`$ での主張つきの AGREE⁺（§2.2）。成り立つもの：FRAG2$`^{\mathrm{rel}}`$、DECOUPLE、BASE-INV$`^{\mathrm{reg}}`$、FIX″、IDX″、TAIL″、補題としての LONG-RS$`^{\mathrm{rel}}`$、MIN$`^S`$ つきの Carlson の範疇性の定理、LEAST、CAT、CAT-$`\beta_0`$、CAT-E、O$`^S`$、C-TRANSFER$`^{\mathrm{RIG}}`$、GHOST-SHAPE、素の符号。FRAG のもとで、主張は $`R_2^C`$ で $`[0, X_{21}]`$ で証明済み。**のちに（41 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §1.1）：** FRAG のもとで $`\nu_C = \nu_S = L(\omega+1)`$ と $`[0, \nu_C]`$ での主張がもう一度証明された。$`\nu_C`$ より上の区間の中のちょうどの計算はまだやり直していないので、このページの $`\nu_C`$ より上の結果は書いたままでは証明されていないまま。

**のちに（42 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §2.1、§2.2）：** 区間の計算を直した値でやり直した。定理 B$`^\nu`$ と $`L(\omega^2)`$、FRAG″ (d)、FRAG2″、定理 C″ と $`L(\Omega_1\cdot\omega)`$、CAP-SUPPLY (ii)、$`L(\varepsilon_{\Phi_\Omega+1})`$ は $`R_2^C`$ でもう一度証明された（FRAG のもと、やり直しで査読 1 回）。§1.2 と §2.2 の $`R_2^S`$ の側は 1 行ずつはやり直していない（概略）。$`R_2^S`$ では主張は今は FRAG のもとで $`[0, F_\nu)`$ で成り立つ（[SHIFT11-ja.md](SHIFT11-ja.md) §2.2）。**のちに（43 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §3.2）：** $`R_2^S`$ では主張は FRAG のもとで $`[0, Z^\Lambda)`$ で成り立つので、このページの $`R_2^S`$ での範囲は覆われる。

## 1. 33 回目

3 つの論文（2026-10）。どれも 1 回ずつ査読された：定理 B$`^\nu`$ を直し、点 $`L(e)`$ の骨組みに沿って先へ進む論文（§1.1）、監査の残りと $`\nu`$ の上の $`R_2^S`$ の論文（§1.2）、
素の符号の論文（§1.3）。この節の結果は、回数を書いていなければ査読 1 回。定理 B$`^\nu`$（$`[0, L(\omega^2)]`$ での主張）は初めの 2 つの論文がそれぞれ独立に証明したので **査読 2 回**。
[SHIFT7-ja.md](SHIFT7-ja.md) §3 の 3 つの査読の細かい点はこれらの論文が反映し、この回の査読者がそれぞれの直しを確かめた（**査読 2 回**）。どの論文も Wilken, JSL 72 (2007)、
Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない（査読者が確かめた）。§1.1 と §1.2 で引く論文：[W07b]（Cor 5.10。L.2.1 と Thm 2.2 はこの計画自身の証明を通してだけ）、
Carlson 2009（Def 5.3 の 2 つ目の条件、L.2.5、L.5.5、Thm 14.14）、Wilken 2020（L.21.7、L.21.10、L.21.12 (1)、Prop. 21.6、Prop. 21.11）。査読者はどの引用も論文の本文と照らし合わせた。
§1.3 の証明済みの段階はどの論文も使わず、FRAG も使わない。$`\psi`$ についての事実は InaccPsi の Lean の展開から取る（査読者が引いたどの行も leanman で確かめた）。Lean のファイルは
足していない：§1.1 の論文は、順序数の入力を項を比べるだけの Lean のファイルで確かめた（`#eval`、定理は無い。緑で、査読者の再実行でも同じ出力）。これは確かめた扱い。段の番号は
[SHIFT7-ja.md](SHIFT7-ja.md) と同じ（論文より 1 つ大きい）。「FRAG のもと」は、FRAG と FRAG-SUBST、SUBST-COMM、[W07b] Thm 2.2 のこの計画自身の証明をあわせたもとで、という意味。

記号（[SHIFT7-ja.md](SHIFT7-ja.md) §3.2 と同じ）：$`L(e) = H(\eta_e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$、$`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$。$`L(e)`$ の区間は $`[L(e), L(e+1))`$。$`\nu = L(\omega+1)`$。**骨組みの
やり直し** とは、$`\lambda''`$ が $`\omega^2`$ の 0 でない倍数である $`L(\lambda'')`$ のこと。その組は $`\tau''_j = L(\lambda''+\omega\cdot j)`$、$`\delta''_j = L(\lambda''+\omega\cdot j+1)`$（$`j \ge 1`$）、その **骨組みの符号** は
$`c''(\lambda'') = -1 + \mathrm{logend}(\lambda'')`$。**基の点** とは、どの $`\alpha \lt p`$ でも $`\mathrm{lh}(\alpha) \lt p`$ となる $`p`$ のこと。やり直し $`R`$ の **蓋の点** は $`H(\eta_R + \Lambda_R + \omega^2)`$。

### 1.1 FRAG のもとで、定理 B$`^\nu`$ と、$`L(\Omega_1\cdot\omega)`$ までの点 $`L(e)`$ の骨組み

- **[SHIFT7-ja.md](SHIFT7-ja.md) §3.2 への査読の直し**（その進行を止める点 B-1 と細かい点 m1、m2、m4）。DECOUPLE：$`+`$ についての部分は蓋より下だけに残す（m4。証明済み）。
  FRAG2$`^{\mathrm{rel}}`$（証明済み、FRAG のもと）：FRAG2 の証明は、骨組み型の仮定を「どの $`\lt_2`$ の組も両端が $`\upsilon`$ の点」という形でしか使わず、それは $`R_2^S`$ のどの可算の段階でも
  成り立つ。だから FRAG2 は、動かない集合に組があっても $`\nu`$ より上で成り立つ (m2)。BASE-INV$`^{\mathrm{reg}}`$（証明済み）：動かない点 $`x`$ では、$`\mathrm{lh}(x) \lt \rho_R`$（動く点との関係は両側で偽）か
  $`x \le_1 \rho_R`$（帰納法の中で両側で真）のどちらか。点 $`L(e)`$ の届く先は要らないので、循環した場合は消えた (m1)。GAP-CALC$`^{\mathrm{reg}}`$（移しで証明済み、FRAG のもと）：段 2 の
  ちょうどの計算は、区間の中の、蓋の点が今の上限 $`y`$ 以下であるどのやり直し $`R`$ でも成り立ち、区間の終わりには条件が無い（[SHIFT7-ja.md](SHIFT7-ja.md) §1.1 の CAP-1 の区域の形。これが
  B-1 の直し）。
- **定理 B$`^\nu`$**（移しで証明済み、FRAG のもと。§1.2 とあわせて **査読 2 回**）。どの $`j \ge 1`$ でも $`R_2^S`$ と $`R_2^C`$ で $`L(\omega\cdot j) \lt_2 L(\omega\cdot j+1)`$。これらが右端が $`L(\omega^2)`$ より下の
  新しい組のすべて。$`L(\omega^2)`$ より下のどのやり直しもちょうどの届く先を持つ。$`\beta_0 \gt L(\omega^2)`$。だから **$`R_2^C`$ での Wilken の主張は $`[0, L(\omega^2)]`$ で成り立つ**、$`L(\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+2})`$。
  止まっていた段階 LOW$`_j`$（蓋 $`L(\omega\cdot(j-1)+1)`$ の上の最小の上端は $`L(\omega\cdot j+1)`$ 以上）は今は成り立つ：左端 $`x`$ の $`\le_1`$ の前の点 $`u`$ が区間の中にあれば、区域の条件を満たす
  ので、GAP-CALC$`^{\mathrm{reg}}`$ から $`u`$ は自分を越えない。ところが越える。だから前の点は点 $`L(e)`$ で、$`x = L(e_x)`$、$`e_x`$ は極限。$`R_2^C`$ の側：KAPPA と C-TRANSFER（$`Z`$ より下で $`R_2^S`$ が
  点 $`L(e)`$ について骨組み型なら $`\beta_0 \gt Z`$）。
- **FRAG″**（(a)–(c) は証明済み、FRAG のもと。(d) と FRAG2″ は移しで証明済みで、最前線より下だけ、細かい点 m2）。有限個の点 $`L(e_1) \lt \dots \lt L(e_m)`$ を、それぞれの区間ごと、
  下の写像つきの BC$`^\pi`$ の η の基の取りかえで、一度に $`L(e'_1) \lt \dots \lt L(e'_m)`$ に動かす。合わせた写像は、有限の遺伝的な閉包の $`\upsilon`$ の点での定理 FRAG の写像（FRAG-SUBST″）。
  $`R_1^+`$ の $`0, +, \le, \le_1`$、$`\upsilon`$ の点、やり直し、ブロックの上端（SUBST-COMM″）と、区間の中のやり直しのちょうどの届く先（TC⁺″）を保つ。FRAG2″：それが $`\le_2`$ を保つのは、
  動く点 $`L(e)`$ の届く先と、動く端を持つ組を保つときちょうど。
- **FIX″、IDX″、TAIL″**（証明済み。査読者が 67 個の見本で確かめた）。$`L(\Omega_1\cdot k)`$ は $`e \mapsto L(e)`$ の $`k`$ 番目の不動点で、繰り返し $`e_{n+1} = L(\Omega_1\cdot(k-1) + e_n)`$ の上限。
  最小のものは $`L(\Omega_1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1})`$。$`\Omega_1\cdot\omega`$ より下では $`L`$ はその定義域で狭義に増え、連続。
- **骨組みのやり直しの計算**（BLOCK″$`_0`$、EXACT-C″、EXACT-Ω″、CAP″。移しで証明済み、FRAG のもと）。$`\lambda'' \lt \Omega_1\cdot\omega`$ の骨組みのやり直し $`L(\lambda'')`$ と
  $`\delta''_1(\lambda'') = L(\lambda''+\omega+1)`$ について：

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + c''(\lambda'')\ \ (c''(\lambda'') \text{ countable}),\qquad r(L(\Omega_1\cdot k)) = \delta''_1(\Omega_1\cdot k) + L(\Omega_1\cdot k).
```

  たとえば $`r(L(\omega^2)) = L(\omega^2+\omega+1) + 1`$、$`r(L(\Omega_1)) = L(\Omega_1+\omega+1) + L(\Omega_1)`$。これは EXACT-C（$`r = \delta + (-1 + e)`$）と EXACT-W の最初の場合（$`r = \delta + \rho`$）を 1 つ上に
  上げたもので、$`-1 + e`$ の代わりに骨組みの符号、$`\rho`$ の代わりに点 $`L(\lambda'')`$ そのものが入る。
- **定理 C″**（移しで証明済み、FRAG のもと）。$`L(\Omega_1\cdot\omega)`$ より下で、$`R_2^S`$ は点 $`L(e)`$ の骨組みについて骨組み型（[SHIFT7-ja.md](SHIFT7-ja.md) §3.2 の予想 SKEL″ がそこで
  成り立つ）：どの新しい組も組 $`(\tau''_j, \delta''_j)`$ で、新しい組を含まない。骨組みのやり直しでない点 $`L(e)`$ はちょうどそのブロックの上端に届く。$`L(\Omega_1\cdot\omega)`$ より下のどの
  やり直しもちょうどの届く先を持つ（段 2 の符号で $`P' + \Omega_1`$ まで）。その下に扇の頂点も 3 重の入れ子も無い。
- **新しい最前線**（移しで証明済み、FRAG のもと）。右端が $`L(\Omega_1\cdot\omega)`$ より下のどの関係でも $`R_2^C = R_2^S`$（$`\beta_0 \gt L(\Omega_1\cdot\omega)`$）。3 重の入れ子の最小の上端は両方の構造で
  その上にある。そして **$`R_2^C`$ での Wilken の主張は $`[0, L(\Omega_1\cdot\omega)]`$ で成り立つ**。両方の半分とも（名前の側はその点が標準形だから、補題 L）：

```math
L(\Omega_1\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1+1}).
```

- 査読者の細かい点（どれも結果を変えない）。$`\beta_0 \gt L(\Omega_1\cdot\omega)`$ を与える段階は、最前線そのものを上限として GAP-CALC$`^{\mathrm{reg}}`$ を引くが、そこではその仮定は偽
  （組 $`(\tau''_j, \delta''_j)`$ がそこで終わる）。その結論はブロックごとに成り立ち、使うのはそれだけ (m1)。FRAG″ の (d) と FRAG2″ は $`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ より下のどの $`L(e)`$ についても書かれているが、
  証明は最前線より下だけで、使うところはどれもそこ (m2)。論文は監査の残り R-1 を済んだものとして挙げる。それは §1.2 に書かれた (m3)。評価 $`\Lambda + \omega^2 \lt \omega^m`$ は符号
  $`m \le 2`$ で偽だが、使う不等式は成り立つ (m4)。BASE-INV$`^{\mathrm{reg}}`$ は区間の中のやり直しについて書かれ、点 $`L(e)`$ で使われる。証明は同じ (m5)。言い回しと、定義域の外の添字での包に
  ついての書かれていない事実。$`L(\Omega_1)`$ は $`L`$ の定義域に属さない（m6、m7）。確かめの 1 つの族は BASE-INV$`^{\mathrm{reg}}`$ で済むが書き出されていない (m8)。
- **未証明**（概略か予想）。EXACT-W″：$`r(L(\Omega_1\cdot\omega)) = L(\Omega_1\cdot\omega+\omega+1) + L(\Omega_1\cdot\omega) + 1`$（概略だけ。34 回目に証明された、§2.1）。これがあれば最前線は
  $`L(\Omega_1^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1\cdot 2})`$ に動く。$`\Omega_1\cdot 2`$ 以上の骨組みの符号、骨組みの長いやり直し、符号 $`P_3`$、$`\nu_3`$：未解決か予想（LIFT$`_2`$：$`[0, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ の
  解析が、$`(\Omega_\omega, \theta)`$ を $`(\Omega_\omega\cdot 2, P')`$ に置き換えて骨組みに移る）。

### 1.2 監査の残りと、$`\nu`$ の上の $`R_2^S`$

- **LONG-RS$`^{\mathrm{rel}}`$**（証明済み、FRAG のもと。査読者の m1、m2 を入れて。[SHIFT7-ja.md](SHIFT7-ja.md) §3.1 の監査の残り R-1）。やり直しの符号以下の $`c \lt \Omega_2`$ のどの符号でも、
  $`\omega^c`$ より下の η のずれをまたぐ長いやり直しの段階。どの段でも、どの蓋の上でも成り立つ。その移しは複写無しの基の取りかえで、動かない点は XA$`^p`$、基の取りかえは
  FRAG2$`^{\mathrm{rel}}`$ で扱う。CAP-SUPPLY が $`P'`$ より下のどの符号でもその届く先の仮定を与える。R-1 が挙げた使い方はどれもその場合で、CROSS-LIM もその 1 つ。査読者：XA$`^p`$ は
  書いたままでは偽。その上限は、やり直しでない動かない点 $`x`$ の $`\mathrm{lh}(x)`$ も超えなければならない（反例つき。m1）。符号が $`\pi`$ の符号であるやり直しでは $`c = D' + 1`$ と取る (m2)。
  どちらの直しも 1 行。だから $`\nu_C`$ への鎖が書かずに使っていた補題は今は書かれた（[AUDIT-ja.md](AUDIT-ja.md)）。
- **2.6′ と TC⁺$`^{\mathrm{rel}}`$**（移しで証明済み。R-2 と L3-b）。計算の移しの等式は複写無しの基の取りかえ（「裸の基」）でも成り立ち、$`P'`$ より下のどの符号でも届く先はその
  基の取りかえと入れかわる。CROSS-LIM、TC⁺$`^\omega`$、PAIR$`_j`$ の引用は今はこれを引く。
- **段 2 での確かめの行**（移しで証明済み。L2-a、L1-b、L2-b）。段 2 に移したどの命題にも、置き換えた入力を書いた行が 1 つある。添字 $`\eta`$ によるどの段階も知られた 6 つの種類の
  どれかで、どれも段 2 で与えられる。査読者は行の見本を確かめた（すべての行ではない）。
- **$`\theta`$ より先の CNST$`_j`$**（確かめた。L1-a）。可算の定数つきで、形をじかに読んで：最初のしきいで 1,597 個の部分形、その上で 449 個と 48 個、失敗 0。規則を壊した 2 つの版は
  1,321 回と 542 回失敗する。査読者：新しい種で 4,632 個の部分形、失敗 0、そして構造からの理由。順序の試しは整合の確かめにすぎない（その対照が鈍い）。48 個はたぶん 24 個の
  1 つの集合を 2 度数えたもの (m6)。
- **AGREE$`^\nu`$**（移しで証明済み、FRAG のもと）。$`y^C_\nu = y^S_\nu = L(\omega\cdot 2+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1}\cdot 2 + P')`$：$`[\nu, y^C_\nu]`$ で 2 つの構造に違いは無く、
  $`\beta_0 \gt L(\omega\cdot 2+1)`$。だから [SHIFT7-ja.md](SHIFT7-ja.md) §3.2 の定理 A$`^\nu`$ はちょうどの上端で成り立つ。同じ文をどの $`j`$ でも使うと定理 B$`^\nu`$ の 2 つ目の証明になる。
  $`\beta_0`$ そのものの場所は分かっていない。
- 査読者のほかの細かい点：無限の $`m`$ では $`1 + m = m`$ だが評価は成り立つ (m3)。定義域の条件の 1 つは CODE-ORD から出るが論じていない (m4)。2 つの段をまたぐ $`m^*`$ での越え方には
  確かめの行が無い（m5。ここでは使わない）。言い回し (m7)。

### 1.3 素の符号：$`\Omega_{\omega+1}`$ の単位と $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$

[SHIFT7-ja.md](SHIFT7-ja.md) §3.3 と同じく $`S_1 = \Omega_\omega`$、$`S_{m+1} = \psi_{\Omega_{\omega+1}}(\Omega_\omega\cdot S_m)`$、$`\sigma_{\omega+1} = \sup_m S_m = \psi_{\Omega_{\omega+1}}(\Omega_{\omega+1})`$ と書く。

- **[SHIFT7-ja.md](SHIFT7-ja.md) §3.3 への査読の細かい点を反映した**（**査読 2 回**）：例の項 (m1)、形式的な飾り $`A(z)`$ (m2)、ATOM-SUP の範囲の仮定 (m3)、「移しで」の札 (m4)、
  言い回し（m5、m7）。証明書の支えの無い宿し方は、手で証明したと書いた (m6)。
- **順序数の側**（証明済み。STAGE$`^{SS}`$ と PUSH$`^{SS}`$ は移しで）。$`[\sigma_{\omega+1}, \Omega_{\omega+1})`$ の段階はどの有限の段でも良くない（BAD-INT）。$`T \lt \sigma_{\omega+1}`$ の段階 $`\Omega_{\omega+1} + T`$ は
  良い（GOOD$`^{\omega+1}`$）。どの $`j \ge 1`$ でも $`\psi_{\Omega_j}(\Omega_{\omega+1}) = \sup_m \psi_{\Omega_j}(S_m)`$（SUP-(ω+1)$`_j`$）。段階の系は、良くない区間を除いても働く。そして（SUP-W1S）

```math
\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1}) = \sup_m \psi_{\Omega_1}(\Omega_{\omega+1} + S_m).
```

- **$`\Omega_{\omega+1}`$ の単位**（移しで証明済み）。$`x \lt_2 y`$、$`c \le_1 c\cdot 4`$、$`r, x \le_1 c\cdot 4`$ の単位 $`r \lt x \lt y \lt c`$ は、[SHIFT7-ja.md](SHIFT7-ja.md) §3.3 の普遍な上端の単位を区域の
  いちばん上の単位として使ったもの。その宿しの補題 OMEGA-SUP は前の普遍な宿しの補題と一字一句同じ（査読者：札は「引用」にすべき）。部品の上端は $`c\cdot 5`$ に動く。符号の鎖の数は 3 の
  ままなので、MODULE-RED$`_4`$ で、素の符号で：

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1} + \psi_{\Omega_{\omega+1}}(\Omega_{\omega+1})) \gt \psi_{\Omega_1}(\Omega_{\omega+1} + 1),
```

  そしてこの点より下で $`\mathrm{CH}_4`$ で RED-TOWER が成り立つ。$`\mathrm{CH}_3`$ の評価は $`\psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ のまま。どれも下からの評価だけ。
- **この道の最前線**（FRONTIER、STAGE のもとで証明済み）。$`\Omega_{\omega+1} + \sigma_{\omega+1}`$ より先のどの段階の集合もその段階を含み、その原子 $`\sigma_{\omega+1}`$ は区域自身の $`\Omega_{\omega+1}`$ を引数に持つ。
  今ある単位の種類はどれもそれを符号にしない（注意で、定理ではない）。予想 REF：単位の組の中の印の点が $`\Omega_{\omega+1}`$ の代わりになり、鎖の数 4 で $`\psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2)`$ まで
  届く。その宿しの補題 REF-SUP は未解決。
- **$`\theta_0`$ への順序数の側**（証明済み）。どの基の要らない $`\rho`$ でも SUP-(ρ+1)（移しで）。$`\psi_{\Omega_1}(\Omega_{\omega\cdot 2}) = \sup_n \psi_{\Omega_1}(\Omega_{\omega+n})`$。$`t_{m+1} = \psi_{\Omega_1}(\Omega_{t_m+1})`$ で
  $`\psi_{\Omega_1}(\Omega_{\Omega_1}) = \sup_m t_m`$（査読者が 1 つの段階を書き直したあとで、m1）。$`u_1 = \Omega_1`$、$`u_{m+1} = \Omega_{u_m}`$ で $`\psi_{I_0}(0) = \sup_m u_m`$、$`\theta_0 = \sup_m \psi_{\Omega_1}(u_m)`$。だから素の側は
  $`\theta_0`$ の前に 2 つの道具が要る：どの添字でも $`\Omega`$ を指すこと、そして自身の引数の符号を添字にした $`\Omega`$ の単位。どちらも未解決。
- 査読者のほかの細かい点：見出しは SUP-(ρ+1) を言いすぎ。証明は基の要らない $`\rho`$ だけ (m2)。$`\Omega_{\omega+1}`$ の単位はその区域のいちばん上（最後）の単位 (m3)。FRONTIER の 1 つの文は
  書いたままでは偽で、見出しは FRONTIER より多くを言う (m4)。STAGE$`^{SS}`$ の置き換えた事実を書くべき (m5)。札 (m6)。OMEGA-SUP の証明書の支えは査読者の模型の証明書だけ (m7)。

### 1.4 33 回目のあとの状態

§2.4 で置き換えた。

- $`R_2^C`$ での Wilken の主張：FRAG 無しで $`[0, X_4]`$、そして **FRAG のもとで $`[0, L(\Omega_1\cdot\omega)]`$、$`L(\Omega_1\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1+1})`$** で両方の半分とも成り立つ
  （$`[0, X_{21}]`$ は査読 2 回。$`\nu_C = \nu_S = L(\omega+1)`$ までは査読 1 回と監査で、監査の残りは今は書かれた、§1.2。$`\nu_C`$ から $`L(\omega^2)`$ までは査読 2 回で 2 つの証明。$`L(\omega^2)`$ から
  $`L(\Omega_1\cdot\omega)`$ までは査読 1 回、§1.1）。
- $`R_2^S`$ と $`R_2^C`$：右端が $`L(\Omega_1\cdot\omega)`$ より下のどの関係でも 2 つは一致し、$`y^C_\nu = y^S_\nu = L(\omega\cdot 2+1)`$（FRAG のもと）。$`\beta_0`$ の場所は分かっていない。
- 届く先（FRAG のもと）：$`L(\Omega_1\cdot\omega)`$ より下のどのやり直しでもちょうど。
- **LOW：FRAG のもとで偽**。**LOW$`^\infty`$：FRAG のもとで真**（どちらも査読 1 回。変化なし）。
- $`\theta_0`$ より下の下からの評価の計画：素の評価 $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ と $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$（どちらも査読 1 回）。SRO より下の段階：
  変化なし（3,166 個の標本の行列すべてでどの $`n`$ でも。SRO より下のすべての標準の行列についての一般の命題は未解決）。

### 1.5 33 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。$`\omega^2`$、$`\omega^3`$、$`\omega^\omega`$、$`\varepsilon_0`$、$`m^*`$、$`\Omega_1`$、$`\Omega_1\cdot 2`$ の区域の点、不動点 $`L(\Omega_1\cdot k)`$、$`L(\Omega_1\cdot\omega)`$ の名前、標準形、添字が定義域に属すこと、順序。
  対照（定義域に属してはならない添字）は属さない。Lean は緑で Python と同じ。査読者：67 個の見本で FIX″、80 個の場合で EXACT-C″ の行き先、10 個の場合で CROSS-LIM″ の実現するもの、
  どれも成り立つ。Lean の再実行は同じ出力。
- §1.2。上の数。査読者は m2 の前提を 6 個の $`\pi`$ の符号で確かめ（6 個中 6 個）、[SHIFT7-ja.md](SHIFT7-ja.md) §3.2 の Lean のファイルを再実行した（同じ出力）。
- §1.3。2 つの種でそれぞれ名前の 111 個の確かめ、失敗 0。$`\Omega_{\omega+1}`$ の単位を持つ 6 個の符号と上端は鎖の数 3、変異体は 4。証明書（再生した）：前向き 5 個中 2 個、$`\mathrm{CH}_4`$ より
  下の上端は見つかった。普遍な単位による宿しと、新しい引数の符号を持つ 2 つの宿しは 45 秒で時間切れ。逆向き 3 個中 0 個。査読者：新しい種で失敗 0。3 つの種で自前の試し（良くない
  段階およそ 1,560 個、良い段階およそ 6,400 個、上限の補題）、失敗 0。模型の証明書（$`\Omega_{\omega+1}`$ の単位が $`\psi`$ の単位を宿す）は見つかり、逆向きは見つからない。

### 1.6 未解決

§2.6 で置き換えた。

- FRAG のもとで $`L(\Omega_1\cdot\omega)`$ より上の主張（FRAG 無しでは $`X_4`$ より上）。次は $`L(\Omega_1\cdot\omega)`$ での EXACT-W″、そのあと $`L(\Omega_1^2)`$。そのあと $`\Omega_1\cdot 2`$ 以上の骨組みの符号、
  骨組みの長いやり直し、符号 $`P_3`$、$`\nu_3`$。$`R_2^S`$ で：FRAG 無しで $`\nu`$ より上の段の $`o_k = \omega`$。
- 2 つの段をまたぐ $`m^*`$ での越え方を、確かめの行つきの独立の段階として書くこと（§1.2 の細かい点 m5）。
- $`L(\Omega_1\cdot\omega)`$ より上の $`R_2^S = R_2^C`$ と、$`\beta_0`$ そのもの。$`\upsilon_{\omega^3}`$ より上の $`R_2^S`$ での核の側。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と $`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数：$`\varepsilon_{\Omega_\omega+1}`$ より先の鎖の数 3。$`\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$ より先は指す点 REF（行き先 $`\psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2)`$）、そのあと $`\Omega_{\omega\cdot 2}`$、
  $`\Omega_{\Omega_1}`$、$`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。$`\nu`$ より上の、$`\upsilon`$ の点でない点の名前。
  [COVER-ja.md](COVER-ja.md) §9 の残り。

## 2. 34 回目

3 つの論文（2026-10）。どれも 1 回ずつ査読された：$`L(\Omega_1\cdot\omega)`$ の届く先と $`\varepsilon_{\Phi_\Omega+1}`$ までの骨組みの符号の論文（§2.1）、Carlson の範疇性の定理を使って $`R_2^S`$ と $`R_2^C`$ を
比べる論文（§2.2）、素の符号の論文（§2.3）。この節の結果は、回数を書いていなければ査読 1 回。$`[0, Z^+]`$ での主張（記号は下）は初めの 2 つの論文がそれぞれ独立に証明したので、
$`L(\Omega_1\cdot\omega)`$ から $`Z^+`$ までの段階は **査読 2 回**。§1 の 3 つの査読の細かい点はこれらの論文が反映し、この回の査読者がそれぞれの直しを確かめた（**査読 2 回**）。どの論文も
Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない（査読者が確かめた）。引く論文：§2.1 は §1 と同じく査読済みの段階を通してだけ。§2.2 は
T. J. Carlson, "Categoricity for patterns of order 2", https://arxiv.org/abs/1104.1686（[C11]：範疇性の定理、その証明の中の Claim 1、Cor 0.8、Cor 0.9）と Carlson 2009（Def 5.3 の 2 つ目の条件、
L.5.5、L.14.9、Thm 14.10、Thm 14.14）。[C11] は arXiv の preprint で、査読されていない。査読者はその Claim 1 をやり直し、そこで「すぐ分かる」とされた段階（重なりの上で写像がきちんと
決まること）を書き出し、どちらも成り立った。§2.3 の証明済みの段階はどの論文も使わず、FRAG も使わない。Lean のファイルは足していない：§2.1 と §2.2 の順序数の入力は項を比べる
だけの Lean のファイルで確かめた（`#eval`、定理は無い。緑で Python と同じ出力）。§2.3 は引いた InaccPsi の補題の文を確かめた（`#check`）。これらは確かめた扱い。段の番号は §1 と同じ
（論文より 1 つ大きい）。「FRAG のもと」は §1 と同じ。

記号（§1 と同じ）：$`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$（[SHIFT2-ja.md](SHIFT2-ja.md) §2）、そして

```math
Z^+ = L(\Omega_1\cdot\omega+\omega+1) = \delta''_1(\Omega_1\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1+1} + \omega^{P'+1} + P').
```

骨組みの符号 $`c`$ と点 $`b`$ について、$`c[\Omega_1 := b]`$ は $`c`$ の $`\Omega_1`$ を $`b`$ に置き換えたもの（$`\Gamma_{\Omega_1+1+\beta} = \psi_{\Omega_2}(\beta)`$ は $`\Gamma_{b+1+\beta}`$ に、$`\Phi_\Omega`$ は $`b`$ より上の
$`\alpha \mapsto \Gamma_\alpha`$ の最小の不動点になる）。$`L`$ の定義域とは、$`\eta_e`$ が $`\upsilon`$ の点の添字になる $`e`$ の集合。

### 2.1 FRAG のもとで、$`L(\Omega_1\cdot\omega)`$ の届く先と、$`L(\varepsilon_{\Phi_\Omega+1})`$ までの主張

- **§1.1 への査読の直し**（m1–m8。**査読 2 回**）。(Z3) と定理 C″ の (b) はブロックごとの形にした：区間の中のどのやり直しも、自分のブロックの基の点と上限で GAP-CALC$`^{\mathrm{reg}}`$ を使い、
  C-TRANSFER が要るのはその結論だけ (m1)。FRAG″ の (d) と FRAG2″ は最前線より下の区間に限った (m2)。長いやり直しの段階はどの使い方でも、査読の m1 と m2 を入れた §1.2 の
  LONG-RS$`^{\mathrm{rel}}`$ を引く。裸の蓋でない基の点でも同じ (m3)。小さい符号での評価、どのやり直しでもの BASE-INV$`^{\mathrm{reg}}`$、言い回し（m4–m8）。
- **$`L`$ の定義域**（DOM″、DOWN″、COF″、TAIL″、FIX2″。証明済み）。どの $`e \lt \varepsilon_{\Phi_\Omega+1}`$ でも、$`e`$ が定義域に属すのは、$`e`$ のどの可算の定数も $`L(e)`$ より下であるときちょうど（DOM″）。
  定義域は標準形の頭の部分について閉じ（DOWN″）、$`L`$ はその極限で連続（COF″）、骨組みのやり直しの尾はより小さい符号を持ち（TAIL″）、$`L(\Omega_1^2)`$ は $`\zeta \mapsto L(\Omega_1\cdot\zeta)`$ の最小の
  不動点（FIX2″）。
- **骨組みの基での道具**（移しで証明済み）。$`\upsilon^*`$ より下の読みの Veblen と $`\Gamma`$ の補題は、その $`\varepsilon`$ の閉包とあわせて、どの $`\upsilon`$ の点でも成り立つ（その証明は上限 $`\upsilon^*`$ を
  使わない）。FRAG の置き換えの写像は、これらの補題が使う射影と同じ。PIN-S″（FRAG 無し）と TOP-REG″（FRAG 無し、帰納法の中で）は基 $`L(\lambda'')`$ での上からの道具。
- **$`L(\Omega_1\cdot\omega)`$ での EXACT-W″**（移しで証明済み、FRAG のもと。§1.1 の概略を、和だけを使って全部書いた）：

```math
r(L(\Omega_1\cdot\omega)) = Z^+ + L(\Omega_1\cdot\omega) + 1.
```

  もっと一般に、$`L(\Omega_1^2)`$ より下で符号 $`\Omega_1 + a`$（$`a`$ は可算）を持つ骨組みのどのやり直しでも $`r(L(\lambda'')) = \delta''_1(\lambda'') + L(\lambda'') + a`$。だから主張は $`[0, L(\Omega_1^2)]`$、
  $`L(\Omega_1^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1\cdot 2})`$ で成り立つ。
- **定理 EXACT-G″**（移しで証明済み、FRAG のもと。$`\lambda'' \lt \varepsilon_{\Phi_\Omega+1}`$ で）。$`\lambda'' \lt \varepsilon_{\Phi_\Omega+1}`$ で符号 $`c = c''(\lambda'')`$ を持つ骨組みのどのやり直し $`L(\lambda'')`$ でも：

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + c[\Omega_1 := L(\lambda'')].
```

  たとえば符号 $`\Omega_1\cdot 2`$ は $`\delta''_1 + L(\lambda'')\cdot 2`$、符号 $`\varepsilon_{\Omega_1+1}`$ は $`\delta''_1 + \varepsilon_{L(\lambda'')+1}`$、符号 $`\Gamma_{\Omega_1+1}`$ は $`\delta''_1 + \Gamma_{L(\lambda'')+1}`$ を与える。これは
  $`\Phi_\Omega`$ より下の符号の読み（定理 EXACT-V、[SHIFT2-ja.md](SHIFT2-ja.md) §2.1）を 1 つ上に上げ、本当の届く先にしたもの。与えた符号に届くずれを持つ最小のやり直しも分かる（ATTAIN″）。
- **定理 C$`^G`$ と新しい最前線**（移しで証明済み、FRAG のもと）。$`L(\varepsilon_{\Phi_\Omega+1})`$ より下で、$`R_2^S`$ は点 $`L(e)`$ の骨組みについて骨組み型：どの新しい組も組 $`(\tau''_j, \delta''_j)`$ で、
  新しい組を含まない。どのやり直しもちょうどの届く先を持つ。扇の頂点も 3 重の入れ子も無い。だから $`\beta_0 \gt L(\varepsilon_{\Phi_\Omega+1})`$、$`R_2^C`$ の 3 重の入れ子の最小の上端はその上にあり、
  **$`R_2^C`$ での Wilken の主張は $`[0, L(\varepsilon_{\Phi_\Omega+1})]`$ で成り立つ**。両方の半分とも（名前の側はその点が標準形だから、補題 L）：

```math
L(\varepsilon_{\Phi_\Omega+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\varepsilon_{\psi_{\Omega_2}(\Omega_2)+1}}).
```

  $`L(\Omega_1^2)`$ とこの点の間に $`L(\varepsilon_{\Omega_1+1})`$、$`L(\psi_{\Omega_2}(0))`$、$`L(\Phi_\Omega)`$、$`L(\omega^{\Phi_\Omega+2})`$ がある。覆われない最初の符号は、その点そのものでの $`\varepsilon_{\Phi_\Omega+1}`$。
- 査読者の細かい点（どれも結果を変えない）。蓋が最前線より下で上に限りなく続くことの証明は、塔 $`t_0 = \Omega_1+1`$、$`t_{n+1} = \omega^{t_n}`$ を使うが、その上限は $`L(\varepsilon_{\Omega_1+1})`$ しか
  与えない。塔は $`t_0 = \Phi_\Omega+1`$ から始めなければならず、主張はそのまま成り立つ (m1)。EXACT-G″ は $`\varepsilon_{\Phi_\Omega+1}`$ より下のどの符号でも、つまり定義域の補題が使えない添字
  $`\lambda'' \ge \varepsilon_{\Phi_\Omega+1}`$ でも書かれていた。上のように限る。使うのはそこだけ (m2)。$`L(\Omega_1\cdot\omega)`$ での段階は §1.1 の移しで、引用ではない (m3)。1 つの段階は $`r(b) \ge \delta''_1`$ を
  証明する前に使う。要るのは $`b \le_1 \rho_\lambda \le_1 g`$ で、それは成り立つ (m4)。確かめの 3 つの行の札が違う (m5)。$`\Phi_\Omega = \omega^{\Phi_\Omega}`$ なので、標準形では $`p`$ と $`\omega^p`$ のどちらを書くかを
  決めておく (m6)。途中の 1 つの点は $`\Phi_\Omega+1`$ までの符号と札が付いているが、覆うのは $`\Phi_\Omega`$ までの符号 (m7。この点はそれ自身が誤りで、無限の $`x`$ では $`-1 + x = x`$ なので札はちょうど正しかった、[SHIFT9-ja.md](SHIFT9-ja.md) §1.1)。
- **未証明**。$`\Phi_\Omega`$ より上の Veblen の閉包（最前線を $`L(\Gamma_{\Phi_\Omega+1})`$ に動かす）：概略。EXACT-O″（ずれは、定数が $`L(\lambda'')`$ より下である $`c`$ より下の符号の順序型）と
  骨組みの長いやり直し（符号 $`\psi_{\Omega_2}(\Omega_\omega\cdot 2 + \psi_{\Omega_3}(\Omega_\omega\cdot 2)\cdot\omega^2)`$ から）：予想。骨組みの長いやり直しの着地の計算、$`P_3`$ より下の符号、$`\nu_3`$：未解決。$`P_3`$ より下の
  どの符号でも計算があれば、1 つ上の段でのずらしの判定法が、上端 $`\psi_{\Omega_1}(\Omega_\omega\cdot 3 + \omega^{P_3+1} + P_3)`$（予想された $`\nu_3`$）の 3 重の入れ子を与える（最小の 3 重の入れ子の上からの評価。
  未証明）。

### 2.2 $`R_2^S`$ と $`R_2^C`$：Carlson の範疇性の定理と $`\beta_0 \gt Z^+`$

言葉は [THETA-ja.md](THETA-ja.md) §8.2 のもの：(E) は $`\kappa_C \le \beta_0`$（予想 CORE-2）、(R) は「$`R_2^S`$ で $`\kappa_C`$ はその上のすべてに $`\le_1`$」、AGR は $`\max(\kappa_S, \kappa_C) \le \beta_0`$。$`\sigma_S`$ は
$`\mathrm{Core}(R_2^S)`$ に属さない最小の順序数。

- **MIN$`^S`$ と LEAST**（引用。[C11] Claim 1 を、その定理を $`R_2^S`$ に当てはめる Cor 0.9 を通して。査読者が証明をやり直した。Claim 1 の「覆い」は被覆の閉じた像と読む）。
  $`R_2^S`$ では、等極小の集合はその閉じたどの被覆よりも点ごとに下。だから $`R_2^S`$ の等極小の集合はその最小の写しで、$`R_2^S`$ の Wilken の核と Carlson の核は同じ。$`R_2^S`$ には
  いくらでも長い有限の $`\le_2`$ の鎖がある（CHAINS$`^S`$、閉非有界の集まりの議論で証明済み）。
- **定理 CAT**（引用。[C11] Cor 0.8。重なりの段階は査読者が書き出した、m5）と **f ≤ id**（証明済み）。$`\mathrm{Core}(R_2^S)`$ と $`\mathrm{Core}(R_2^C)`$ は、言語全体で、$`f(x) \le x`$ となる写像 $`f`$ で
  同型。**CAT-β₀**（証明済み）：$`\beta_0 \ge \sigma_S`$（査読者：証明は条件無しでこれを与える。論文はより弱い $`\beta_0 \ge \min(\sigma_S, \kappa_C)`$ を書く、m2）。
- **CAT-E**（証明済み）。次は同値：(E)。$`\mathrm{Core}(R_2^S)`$ は始めの切片。2 つの核は等しい。AGR。だから (E) から (R) が出る。また定理 CC は上限の形で $`R_2^S`$ でも成り立ち（CC$`^S`$）、
  $`f`$ は $`R_2^S`$ での各配置の最小の上端を $`R_2^C`$ でのものに送る（TOPS）。
- **O$`^S`$**（証明済み）。各段で、$`R_2^S`$ での $`o_k = \omega`$ はその段の留めの命題と同値で、(E) からどの段でも $`o_k = \omega`$ が出る。査読者：この同値はどちらの側も決めない。(R) と
  PINNING は (E) に帰着しただけで、証明されていない (m3)。
- **C-TRANSFER$`^{\mathrm{RIG}}`$**（証明済み）。移しの $`R_2^C`$ の側は Carlson 2009, Def 5.3 の 2 つ目の条件だけを使う：$`R_2^S`$ の側の性質 RIG が成り立つところでは、左端での最初の食い違いは
  起きない。RIG はその左端自身の区間での区間の計算。
- **AGREE⁺**（移しで証明済み、FRAG のもと）。ブロックの計算 BLOCK″$`_0`$ は $`L(\Omega_1\cdot\omega)`$ でも成り立つ（添字 $`\Omega_1\cdot\omega`$ での §1.1。$`L(\Omega_1\cdot\omega)`$ の届く先は読まない）。だから
  $`\beta_0 \gt Z^+`$、$`R_2^C`$ の 3 重の入れ子の最小の上端は $`Z^+`$ より上、主張は $`R_2^C`$ で $`[0, Z^+]`$ で成り立ち（§2.1 とあわせて 2 つ目の証明）、**$`R_2^S`$ での主張は $`[0, L(\Omega_1\cdot\omega))`$ で
  成り立つ**（前は $`\upsilon_{\omega^3}`$ まで）。
- **GHOST-SHAPE**（証明済み。査読者の直し m1 を入れて）。(E) が成り立たなければ、$`R_2^C`$ の余分な組 $`(\alpha, \beta_0)`$ の形は 2 つのどちらか。型 N：$`\alpha`$ は $`\beta_0`$ の最後の $`\le_1`$ の前の点で、
  $`\beta_0`$ は $`\alpha`$ の $`R_2^S`$ での届く先の真に内側にある。$`\alpha \lt x_F^C`$（$`R_2^C`$ の最小の扇の頂点）なら、$`R_2^S`$ で $`\alpha`$ は $`(\alpha, \beta_0)`$ に $`\lt_2`$ の後の点を持たない。型 F：$`\alpha`$ は
  $`R_2^C`$ の扇の頂点で、$`\alpha \ge x_F^C \gt T_\omega`$。$`x_F^C`$ より下では型 N しかありえず、それは RIG が成り立つところでは起きない。$`\beta_0`$ の場所は分かっていない（予想：$`\beta_0 \ge x_F^C`$）。
- 査読者のほかの細かい点。3 つの文は証明済みと札が付いているが、注意か予想：2 つ目の条件は $`\Pi`$ 型の証拠を「見られない」こと、扇の区域が移しが「構造の理由で」止まる最初の
  ところであること、問題の左端が入れ子の左端であること。証明されているのは、型 F ではどの $`\Sigma_2`$ の証拠も $`[d, \beta_0)`$ に入ること（$`d`$ は $`\beta_0`$ の最後の $`\le_1`$ の前の点）と、型 F には $`R_2^C`$ の
  扇の頂点が要ること (m4)。次の段階の表の 1 つの行は、最小の長い組でだけ成り立つ (m6)。注意 (m7)：Carlson 2009, p. 97 は、$`\Sigma_n`$ の定義と Def 5.4 が同値だと証明無しに言い、
  Def 5.3 のあとの注意は INC を主張する。どちらもここでは未解決のまま。
- **計画の項目**。MIN$`^S`$：閉じた（引用、[C11]）。場合 P3b は FRAG のもとで起きず、FRAG 無しでは $`\mathrm{Core}(R_2^S)`$ に穴を作る。(R) と PINNING：(E) に帰着。(E)：未解決で、今は
  「$`\mathrm{Core}(R_2^S)`$ に穴が無い」と同値。$`\kappa_C`$ より上の後続の段階での $`\le_1`$ の逆向き：未解決で、核には要らない。

### 2.3 素の符号：桁の単位と $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$

$`\Omega' = \Omega_{\omega+1}`$、$`\psi' = \psi_{\Omega_{\omega+1}}`$、$`\sigma^{(a)} = \psi'(\Omega'\cdot a)`$、$`\sigma_2 = \psi'(\Omega'^2)`$、$`s_1 = \Omega_\omega`$、$`s_{m+1} = \psi'(\Omega'\cdot s_m)`$ と書く。どの $`e \lt \Omega'^2`$ も
$`a, \delta \lt \Omega'`$ で $`\Omega'\cdot a + \delta`$ と書ける。$`a = \omega^{b_1}\cdot k_1 + \dots + \omega^{b_N}\cdot k_N`$ を **上の部分**、$`\delta`$ を下の部分、$`b_i`$ を位置と呼ぶ。

- **§1.3 への査読の細かい点を反映した**（**査読 2 回**。証明書についての言い分は下の m1 で直す）。
- **順序数の側**（証明済み。LIM、STAGE$`^{SS^2}`$、PUSH は移しで。査読者はどの段階も Lean の文と照らした）。$`(\Omega_\omega, \sigma_2)`$ のどの強臨界の $`\theta`$ も、上の部分、位置、下の部分が $`\theta`$ より
  下である $`\psi'(\Omega'\cdot a + \delta)`$（HIGH）。不動点の補題とその CLAIM。どの段でも上限の補題。$`\Omega'^2 + \sigma_2`$ より下の良い段階はちょうど区間 $`[\Omega'\cdot a, \Omega'\cdot a + \sigma^{(a+1)})`$（$`a \lt \sigma_2`$）と
  $`[\Omega'^2, \Omega'^2 + \sigma_2)`$。そして

```math
\psi_{\Omega_1}(\Omega'^2 + \sigma_2) = \sup_m \psi_{\Omega_1}(\Omega'^2 + s_m).
```

- **桁の単位と REF-SUP**（証明済み。§1.3 の予想 REF を形を変えて）。$`\Omega'`$ を指すのは単位自身の組の右端 $`y`$ で、別の印の点は無い。$`\psi'(\Omega'\cdot a + \delta)`$ の単位は

```math
r \lt x \lt A(b_N) \lt \dots \lt A(b_1) \lt A(\delta) \lt y \lt v_N \lt \dots \lt v_1 \lt c,\quad x \lt_2 y,\quad v_i \le_1 v_i + d_{b_i},\quad r, x, c \le_1 c\cdot 3 + v_1\cdot k_1 + \dots + v_N\cdot k_N + d_\delta
```

  で、上の部分の項ごとに桁 $`v_i`$ が 1 つある（$`a = 0`$ は [SHIFT7-ja.md](SHIFT7-ja.md) §3.3 の $`\psi`$ の単位）。REF-SUP：桁の単位はより小さい重さのどの単位も宿す。最初の違いが決める（4 つの
  場合）。新しい桁は宿主の桁での R1 から、新しい位置の符号は宿主の位置の符号での SUP$`^A`$ から来て、客の $`y`$ は組とともに宿主の $`y`$ に行く。$`\Omega'`$ の単位はどの桁の単位も宿し
  （OMEGA-SUP$`^D`$）、$`\Omega'`$ の単位が別の $`\Omega'`$ の単位を宿す必要は無いので、§1.3 の後戻りは起きない。どの単位も組を 1 つだけ持ち、符号の鎖の数は 3 以下。
- **評価**（移しで証明済み。前と同じく、やり直していない前の回の段階の補題による）。素の符号で、$`\mathrm{CH}_4`$ について：

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \psi_{\Omega_{\omega+1}}(\Omega_{\omega+1}^2)) \gt \psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2)
```

  で、REF の行き先を越える。この点より下で $`\mathrm{CH}_4`$ で RED-TOWER が成り立つ。$`\mathrm{CH}_3`$ の評価は $`\psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ のまま。どれも下からの評価だけ。
- **未証明**。裸の桁の版は確かめただけで、証明は書かれていない（m4。それに頼るものは無い）。次の原子 $`\sigma_2`$ の上の部分は、それ自身 $`\Omega'`$ 以上の位置 $`\Omega'`$ を持つ（段階の集合に
  ついての事実として証明済み）。予想 TREE：桁の桁で、新しい組無し、鎖の数 4 で $`\psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1})`$ まで。その先は上の部分の中の Veblen と $`\psi_{\Omega_{\omega+2}}`$ の節。
  $`\psi_{\Omega_1}(\Omega_{\omega+2})`$ にはつぶす節が要り（注意、m3）、それはたぶん $`y`$ より上に組が要るので、鎖の数が増える（予想）。引数の符号を添字にした $`\Omega`$ の単位：概略だけで、順序数の
  側は無い。$`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$、$`\psi_{\Omega_1}(\Omega_{\Omega_1})`$、$`\Omega`$ の塔、$`\theta_0`$：未解決。だから「最初の扇は到達不能基数を要する」は未解決のまま。
- 査読者のほかの細かい点：2 つの種の出力が同じなのは数だけを出すから (m2)。1 つの段階は $`\psi`$ の単調性だけで済む (m5)。新しい符号が宿主の使っていない符号の間に入ることがあるが
  害は無い (m6)。言い回し (m7)。

### 2.4 34 回目のあとの状態

[SHIFT10-ja.md](SHIFT10-ja.md) §3.4 で置き換えた。

- $`R_2^C`$ での Wilken の主張：FRAG 無しで $`[0, X_4]`$、そして **FRAG のもとで $`[0, L(\varepsilon_{\Phi_\Omega+1})]`$、$`L(\varepsilon_{\Phi_\Omega+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\varepsilon_{\Phi_\Omega+1}})`$** で両方の半分とも成り立つ
  （$`[0, X_{21}]`$ は査読 2 回。$`\nu_C = \nu_S = L(\omega+1)`$ までは査読 1 回と監査。$`\nu_C`$ から $`L(\omega^2)`$ までは査読 2 回。$`L(\omega^2)`$ から $`L(\Omega_1\cdot\omega)`$ までは査読 1 回。$`L(\Omega_1\cdot\omega)`$ から
  $`Z^+`$ までは査読 2 回で 2 つの証明、§2.1、§2.2。$`Z^+`$ から $`L(\varepsilon_{\Phi_\Omega+1})`$ までは査読 1 回、§2.1）。
- $`R_2^S`$ での Wilken の主張：FRAG のもとで $`[0, L(\Omega_1\cdot\omega))`$（§2.2）。FRAG 無しでは $`\upsilon_{\omega^3}`$ まで。
- $`R_2^S`$ と $`R_2^C`$：右端が $`L(\varepsilon_{\Phi_\Omega+1})`$ 以下のどの関係でも 2 つは一致する（FRAG のもと）。$`\beta_0 \ge \sigma_S`$。(E) は「2 つの核が等しい」と同値で、(R) を導く。
  MIN$`^S`$ が成り立つ（引用、[C11]）。$`\beta_0`$ の場所は分かっていない。
- 届く先（FRAG のもと）：$`L(\varepsilon_{\Phi_\Omega+1})`$ より下のどのやり直しでもちょうど。
- **LOW：FRAG のもとで偽**。**LOW$`^\infty`$：FRAG のもとで真**（どちらも査読 1 回。変化なし）。予想 CORE-2 の段階 PIN と LOW：決まっていない（変化なし）。
- $`\theta_0`$ より下の下からの評価の計画：素の評価 $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ と $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$（どちらも査読 1 回）。SRO より下の段階：
  変化なし（3,166 個の標本の行列すべてでどの $`n`$ でも。SRO より下のすべての標準の行列についての一般の命題は未解決）。

### 2.5 34 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §2.1。180 個の添字で定義域の判定、140 個の場合で頭の部分、43,200 組で読みの順序、18 個の区域、22 個の行き先、$`L(\Omega_1\cdot\omega)`$ から $`L(\varepsilon_{\Phi_\Omega+1})`$ を経て $`\nu_3`$ までの
  名前の鎖（標準形、添字が定義域に属すこと、増えること）。Lean は緑で Python と同じ。査読者：境目の定数を持つ 1,110 個の乱択の場合で定義域の判定（290 個は定義域の外）、食い違い 0。
  $`\Gamma`$ と $`\Phi`$ の符号での EXACT-G″ の行き先 88 個のうち 87 個が正しく、1 つの失敗は査読者自身の定数の選び方によるもので、証明はそれを除く。120 個の場合で頭の部分。m1 の塔。
  Lean の再実行は同じ出力。
- §2.2。$`L(\Omega_1\cdot\omega)`$ から $`\psi_{\Omega_1}(I_\omega)`$ までの目印の順序。査読者：$`e \lt L(\Omega_1\cdot\omega)`$ の 13 個の添字 $`\Omega_1\cdot\omega + e`$ が定義域に属すこと、16 個の見本で定義域の判定、
  $`L(\Omega_1\cdot\omega)`$ から $`Z^+`$ を経て $`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ までの鎖（標準形、増えること）、それを確かめる Lean のファイル（緑で Python と同じ）。
- §2.3。2 つの種でそれぞれ名前の 310 個の確かめ、失敗 0（査読者：新しい種で 310 個中 310 個。良い段階、HIGH、上限の補題を 2 つの種で自前に試し、失敗 0）。桁の単位を持つ 12 個の符号は
  鎖の数 3、変異体は 4。引いた 11 個の Lean の補題を確かめた（公理は propext、Classical.choice、Quot.sound だけ）。証明書（再生した）：模型の鎖 $`\psi`$ の単位、そして上の部分が $`\omega^0`$、
  $`\omega^0\cdot 2`$、$`\omega^1`$ の桁の単位。$`\Omega'`$ の単位の下の指す単位。査読者は、著者のスクリプトが届かなかった探し方で（m1）：$`\Omega'`$ の単位の下の桁の単位（3 手）、飾りつきの全体の
  符号 3 組のうち 2 組、新しい符号と新しい桁の場合の新しい模型。見つからない：$`\Omega'`$ の単位の下で 2 つ続く新しい桁（証明書の支えが無いだけで、反証ではない）。逆向きの証明書：
  6 個中 0 個（著者）、13 個中 0 個（査読者）。

### 2.6 未解決

[SHIFT10-ja.md](SHIFT10-ja.md) §3.6 で置き換えた。

- FRAG のもとで $`L(\varepsilon_{\Phi_\Omega+1})`$ より上の主張（FRAG 無しでは $`X_4`$ より上）。次は $`\Phi_\Omega`$ より上の Veblen の閉包（最前線 $`L(\Gamma_{\Phi_\Omega+1})`$）、ずれ EXACT-O″、骨組みの
  長いやり直しとその着地の計算、$`P_3`$ より下の符号、$`\nu_3`$。$`R_2^S`$ で：$`L(\Omega_1\cdot\omega)`$ より上の主張。FRAG 無しで $`\nu`$ より上の段の $`o_k = \omega`$。
- 2 つの段をまたぐ $`m^*`$ での越え方を、確かめの行つきの独立の段階として書くこと（§1.2 の細かい点 m5）。
- $`L(\varepsilon_{\Phi_\Omega+1})`$ より上の $`R_2^S = R_2^C`$：(E)、つまり「$`\mathrm{Core}(R_2^S)`$ に穴が無い」こと、そして $`\beta_0`$ そのもの。$`\kappa_C`$ より上の後続の段階での $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と $`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数：$`\varepsilon_{\Omega_\omega+1}`$ より先の鎖の数 3。鎖の数 4 で $`\psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$ より先は予想 TREE（$`\psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1})`$ まで）、そのあと
  $`\Omega_{\omega+2}`$ のつぶす節、引数の符号を添字にした $`\Omega`$ の単位、$`\Omega_{\omega\cdot 2}`$、$`\Omega_{\Omega_1}`$、$`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。$`\nu`$ より上の、$`\upsilon`$ の点でない点の名前。
  [COVER-ja.md](COVER-ja.md) §9 の残り。
