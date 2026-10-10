[← Back](README-ja.md) | [English](SHIFT8.md) | [Japanese](SHIFT8-ja.md)

# $`R_2^+`$ の 33 回目：定理 B$`^\nu`$、$`L(\Omega_1\cdot\omega)`$ までの点 $`L(e)`$ の骨組み、監査の残り、$`\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$ までの素の符号

このページは [SHIFT7-ja.md](SHIFT7-ja.md) の続き（そこの §3 が 32 回目）。§1 が 33 回目。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことの言い直しにすぎないと言った結果は、進みとして数えない。

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
- **未証明**（概略か予想）。EXACT-W″：$`r(L(\Omega_1\cdot\omega)) = L(\Omega_1\cdot\omega+\omega+1) + L(\Omega_1\cdot\omega) + 1`$（概略だけ）。これがあれば最前線は
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

- FRAG のもとで $`L(\Omega_1\cdot\omega)`$ より上の主張（FRAG 無しでは $`X_4`$ より上）。次は $`L(\Omega_1\cdot\omega)`$ での EXACT-W″、そのあと $`L(\Omega_1^2)`$。そのあと $`\Omega_1\cdot 2`$ 以上の骨組みの符号、
  骨組みの長いやり直し、符号 $`P_3`$、$`\nu_3`$。$`R_2^S`$ で：FRAG 無しで $`\nu`$ より上の段の $`o_k = \omega`$。
- 2 つの段をまたぐ $`m^*`$ での越え方を、確かめの行つきの独立の段階として書くこと（§1.2 の細かい点 m5）。
- $`L(\Omega_1\cdot\omega)`$ より上の $`R_2^S = R_2^C`$ と、$`\beta_0`$ そのもの。$`\upsilon_{\omega^3}`$ より上の $`R_2^S`$ での核の側。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と $`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数：$`\varepsilon_{\Omega_\omega+1}`$ より先の鎖の数 3。$`\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$ より先は指す点 REF（行き先 $`\psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2)`$）、そのあと $`\Omega_{\omega\cdot 2}`$、
  $`\Omega_{\Omega_1}`$、$`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。$`\nu`$ より上の、$`\upsilon`$ の点でない点の名前。
  [COVER-ja.md](COVER-ja.md) §9 の残り。
