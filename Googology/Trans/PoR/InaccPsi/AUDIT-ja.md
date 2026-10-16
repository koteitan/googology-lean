[← Back](README-ja.md) | [English](AUDIT.md) | [Japanese](AUDIT-ja.md)

# $`R_2^+`$：$`\nu_C = L(\omega+1)`$ の依存の表（32 回目の監査）

このページは [SHIFT7-ja.md](SHIFT7-ja.md) §3.1 に属する。行 T2b2、T2c1 と最後の節は 33 回目（[SHIFT8-ja.md](SHIFT8-ja.md) §1.2）と 34 回目（そこの §2.1）に更新した。[SHIFT7-ja.md](SHIFT7-ja.md) §2.1 の節目が何に立つかを並べる：

```math
\nu_C = \nu_S = L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P'),\quad\text{and Wilken's claim in } R_2^C \text{ on } [0, \nu_C]\quad(\text{given FRAG}).
```

表は監査のもので、監査の査読者の直し（T2b2 には R-1、S12 には R-3）を入れた。状態の言葉は [README-ja.md](README-ja.md) §3 のもの。「移し」とは、査読済みの証明を、変えたところを
書き出して走らせ直して証明したこと。「査読」は 32 回目のあとの独立した査読の回数。「監査」と書いた節は監査が 1 行ずつ導き直し、その査読者も同意したので、前より 1 回多い。
ほかの節は、監査は場所と札と仮定だけを確かめた。段の番号は [SHIFT7-ja.md](SHIFT7-ja.md) と同じ（論文より 1 つ大きい）。「FRAG のもと」は、FRAG と FRAG-SUBST、SUBST-COMM、
[W07b] Thm 2.2 のこの計画自身の証明をあわせたもとで、という意味。

**監査の判定**：致命的な点も進行を止める点も無い。節目は「移しで証明済み」の水準で成り立つ。見つかった点はどれも細かい（文章、範囲、引用）。

**のちに（40 回目、[SHIFT10-ja.md](SHIFT10-ja.md) §3.2）：** 2 つ目の確かめと 2 人の査読者は、この鎖が、前の値が偽になる符号（$`m_0 \ge \Omega_1`$ のどれでも。たとえば CROSS-LIM がまたぐ符号 $`G_2 + P`$。そして $`2 \le D \lt \hat G`$ での着地）でのちょうどの長い届く先を使うことを見つけた。だから **T0 は書いたままでは証明されていない**。下でそう印をつけた行も同じ。上の判定は置き換えた。影響を受ける符号でのちょうどの長い値を使わない行は成り立つ。FRAG（S13）と FRAG2（S15）は今は引いた 20 個の事実から Lean でも証明済み（[LEAN-ja.md](LEAN-ja.md)）。

**のちに（41 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §1.1）：** 直したちょうどの長い届く先は段 1 と 2 で $`P'`$ より下のどの符号でも証明済み（ENUM-REACH）で、鎖はその上でもう一度走らせた。だから **T0 はもう一度証明された**（FRAG のもと。新しい証明で査読 1 回）。下で「書いたままでは証明されていない（40 回目）」と印をつけた行も、このページの最後の 41 回目の表のとおり同じ。行 S1 と S2 は ENUM-REACH に置き換わる。

**のちに（42 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §2.1）：** $`B_n`$ での段階 TC⁺$`^\omega`$（T2c）は今は EQ$`^{\mathrm{all}}`$ を引くので T0 は書いたままで完全。そして $`\nu_C`$ より上の区間の計算をやり直したので、$`Z^\Lambda`$ までの最前線はもう一度証明された（このページの終わりの 42 回目の表）。**のちに（43 回目）：** 主張は $`R_2^C`$ で $`Z^{\mathrm{FP}}`$ まで進み、査読済みだった段 3 の下からの評価のいくつかは取り下げた（最後の表）。**のちに（44 回目）：** 主張は $`R_2^C`$ で $`Z^{\mathrm{W}}`$ まで、$`R_2^S`$ で $`[0, Z^{\mathrm{FP}})`$ まで進み、$`\nu_3`$ への 43 回目の進行を止める点は片づいた（最後の表）。**のちに（45 回目）：** 主張は $`R_2^C`$ で $`Z^{\mathrm{WW}}`$ まで、$`R_2^S`$ で $`[0, Z^{\mathrm{W}})`$ まで進んだ（その回の表）。**のちに（46 回目）：** 主張は $`R_2^C`$ で $`Z^{\mathrm{V}}`$ まで、$`R_2^S`$ で $`[0, Z^{\mathrm{WW}})`$ まで進み、45 回目の進行を止める点 B-1 は閉じた（最後の表）。

| 節 | 主張 | 場所 | 状態 | 査読 | 立つもの |
|---|---|---|---|---|---|
| T0 | $`\nu_C = \nu_S = L(\omega+1)`$。$`R_2^C`$ の $`[0, \nu_C]`$ での主張 | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | **書いたままでは証明されていない**（40 回目） | 1 と監査 | T1、T2、T3、T4 |
| T1 | 下の半分 $`\nu_C \ge L(\omega+1)`$ | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | **書いたままでは証明されていない**（40 回目） | 1 | T1a–T1d |
| T1a | NU-LOW″：$`x \ge L(\omega)`$ の $`\le_1`$ の前の点は $`[m^*, x)`$ にある | [SHIFT3-ja.md](SHIFT3-ja.md) §2.4 | その条件のもとで証明済み、FRAG のもと | 2 | T1b、T1c、S11 |
| T1b | $`P'`$ より下の CAP-0。LOW は偽 | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | **書いたままでは証明されていない**（40 回目） | 1 | S1 |
| T1c | CAP-1。段 2 でのちょうどの計算（つなぎ L2） | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | **書いたままでは証明されていない**（40 回目） | 2（監査） | S1、S10 |
| T1d | 段 2 での LONG-CLASS$`^\omega`$、LC-STRICT。MULTI-FAR$`_k`$ | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1、§2.1。[SHIFT3-ja.md](SHIFT3-ja.md) §1 | LC-STRICT（不等式）と MULTI-FAR$`_k`$ は証明済み。LONG-CLASS$`^\omega`$ は書いたままでは証明されていない | 1（LC-STRICT は 2） | S1、S3、T1c |
| T2 | 上の半分 $`\nu_C \le \nu_S \le L(\omega+1)`$（PAIR、UP） | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | **書いたままでは証明されていない**（40 回目） | 2（監査） | T2a–T2d |
| T2a | ずらしの判定 SHIFT | [SHIFT-ja.md](SHIFT-ja.md) §1 | 証明済み | 1（その仮定は監査が確かめた） | Wilken 2020、Prop. 21.11 |
| T2b | (C1)、(C2)、(P)：$`L(n) \le_1 L(n+1)`$、$`L(n) \le_1 L(\omega) \le_1 L(\omega+1)`$ | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | **書いたままでは証明されていない**（40 回目） | 2（監査） | T2b1 |
| T2b1 | CROSS-LIM：符号と指数が $`P'`$ 以上のやり直しは $`H(\eta + P')`$ に届く（つなぎ L3） | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | **書いたままでは証明されていない**（40 回目）：符号 $`G_2 + P`$ をまたぐ | 2（監査） | T2b2、T2b3、S2、S10 |
| T2b2 | LONG-RS$`^U`$、今は LONG-RS$`^{\mathrm{rel}}`$：長いやり直しの段階 | [SHIFT2-ja.md](SHIFT2-ja.md) §1.1、§2.1。[SHIFT8-ja.md](SHIFT8-ja.md) §1.2 | どの段でも、$`c \lt \Omega_2`$ の $`\omega^c`$ より下のどの η のずれでも証明済み、FRAG のもと（CAP-SUPPLY、XA$`^p`$、FRAG2$`^{\mathrm{rel}}`$ とあわせて。33 回目に書いた、R-1）。CAP-SUPPLY (ii) は書いたままでは証明されていない（40 回目） | 1。直した形は 2 | S13–S15 |
| T2b3 | どの段でも実現するもの | [SHIFT5-ja.md](SHIFT5-ja.md) §2.2。[SHIFT3-ja.md](SHIFT3-ja.md) §2.4 | 証明済み | 1 / 2 | S11 |
| T2c | (C3)：TC⁺$`^\omega`$、EMB、ONTO-FIN（つなぎ L3） | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | **書いたままでは証明されていない**（40 回目） | 2（監査） | T2c1、T2c2、S1、S12 |
| T2c1 | THETA-EQ$`^{\mathrm{rel}}`$、EQUIV$`^{\mathrm{rel}}`$、EQ-F$`^{\mathrm{rel}}`$。複写の無い基では 2.6′ と TC⁺$`^{\mathrm{rel}}`$（R-2） | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1。[SHIFT8-ja.md](SHIFT8-ja.md) §1.2 | 移し | 1 | S3、S6 |
| T2c2 | どの段でも基の取りかえ BC$`^\pi`$。短い符号での TC⁺。READ-EQ | [SHIFT5-ja.md](SHIFT5-ja.md) §1.2、§2.2 | 証明済み（TC⁺ は FRAG のもと） | 1 | S11 |
| T2d | FIRST-PAIR、蓋 CAP、NU-CT | [BREAK-ja.md](BREAK-ja.md) §2 | 証明済み | 1 | S12 |
| T3 | 核の側：$`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$ | [BREAK-ja.md](BREAK-ja.md) §2 | 証明済み | 1 | S12。Carlson 2009 |
| T4 | 名前の側：$`\nu_C \lt \psi_{\Omega_1}(I_\omega)`$、$`L(\omega+1)`$ の標準形 | [SHIFT-ja.md](SHIFT-ja.md) §1。[SHIFT7-ja.md](SHIFT7-ja.md) §2.5 | 証明済み、確かめた（Lean）。$`\nu_C \le L(\omega+1)`$ は書いたままでは証明されていない | 1 | — |
| S1 | LAND$`^\omega`$：$`P'`$ より下のどの長い符号でもちょうどの届く先とピン（FAR-PIN$`^{L,\mathrm{rel}}`$） | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | **書いたままでは証明されていない**（40 回目）：式は $`m_0 \ge \Omega_1`$ で偽 | 1 | S2、S6–S9 |
| S2 | ちょうどの計算：族、HULL-ARITH、越え方、下からの評価 | [SHIFT6-ja.md](SHIFT6-ja.md) §3 | ちょうどの値は影響を受ける符号で書いたとおりでは偽。**書いたままでは証明されていない**（40 回目） | 1 | S3、S7、S8、T2b2 |
| S3 | THETA$`^\omega`$：$`P'`$ より下のすべての符号の読み方（つなぎ L1） | [SHIFT6-ja.md](SHIFT6-ja.md) §3 | 移し | 2（監査） | S4、S11 |
| S4 | PSI-θ$`^k`$、PSI-W$`^{(k)}`$、PSI-W（つなぎ L1） | [SHIFT6-ja.md](SHIFT6-ja.md) §3.2 | 移し。確かめた（順序だけ） | 2（監査） | S5 |
| S5 | PSI-n、CNST$`^n`$、PSI-θ | [SHIFT3-ja.md](SHIFT3-ja.md) §2.1 | 証明済み | 1 | — |
| S6 | 閉じた点 $`\mathrm{cl}_\nu`$：MONO-cl、AGREE、EQ-cl | [SHIFT6-ja.md](SHIFT6-ja.md) §3.1 | 証明済み | 1 | S7 |
| S7 | EXACT-CL\*、GAP$`_j`$、ENUM | [SHIFT4-ja.md](SHIFT4-ja.md) §2.1 | 証明済み、FRAG のもと | 1 | S13–S15 |
| S8 | FAR-PIN$`^L`$、MULTI-RC$`^L`$、TOP-REG-LAND。下の動くピン、SIM。FAR-PIN$`^{L4}`$ | [SHIFT5-ja.md](SHIFT5-ja.md) §1.1。[SHIFT6-ja.md](SHIFT6-ja.md) §1.2、§2.2 | 移し、FRAG のもと | 1 | S9、S13–S15 |
| S9 | 移し $`T^U`$、FAR-PIN$`^U`$、MULTI-RC$`^U`$ | [SHIFT2-ja.md](SHIFT2-ja.md) §2.1 | 証明済み、FRAG のもと | 1 | S14 |
| S10 | どの段でも道具、TAIL-LEVEL、どの段でも OFF-INF | [SHIFT5-ja.md](SHIFT5-ja.md) §2.2 | 移し（見本の行を確かめた） | 1 | S11 |
| S11 | GEN-ALL。どの段でも D-UNC。SPLIT、DICT、EXT-ETA | [SHIFT5-ja.md](SHIFT5-ja.md) §1.3、§2.2。[SHIFT3-ja.md](SHIFT3-ja.md) §2.4 | 証明済み（EXT-ETA は移し） | 1 / 1 / 2 | — |
| S12 | $`\nu_S`$ より下の SKEL⁺ | [BREAK-ja.md](BREAK-ja.md) §2。[COVER-ja.md](COVER-ja.md) §5.1 | 証明済み | 1（R-3） | — |
| S13 | 定理 FRAG | [RESTARTS-ja.md](RESTARTS-ja.md) §1 | 証明済み。Lean でも（[LEAN-ja.md](LEAN-ja.md)） | 2（監査） | [W07a]、[W07b]、S16 |
| S14 | FRAG-SUBST。SUBST-ISO、SUBST-COMM | [BREAK-ja.md](BREAK-ja.md) §4 | 証明済み | 2（監査）。1 | S13。[W07a] |
| S15 | 定理 FRAG2 | [RESTARTS-ja.md](RESTARTS-ja.md) §2 | 証明済み。Lean でも（[LEAN-ja.md](LEAN-ja.md)） | 2（監査） | S13、S12 |
| S16 | [W07b] L.2.1 と Thm 2.2 のこの計画自身の証明（Wilken, AML 45 の代わり） | 初めのほうの回 | 証明済み | 1 | — |

引くもの。どれも監査が論文の本文と照らし合わせた：[W07a] Def 3.26–3.28、L.3.27、L.3.30、L.4.3、Def 5.1、L.5.3、L.5.5–5.7、Cor 5.4、Def 6.1、Def 6.2、L.6.3、L.6.9、L.6.10。[W07b] L.4.3、
L.4.4、Thm 5.3、Cor 5.7、Cor 5.9、Cor 5.10。Wilken 2020 の Prop. 21.6、L.21.7、Prop. 21.11。Carlson 2009 の L.5.5、L.5.7、Thm 14.10。ここで [W07a] は Wilken, "Ordinal arithmetic based on
Skolem hulling", APAL 145 (2007) 130–161、[W07b] は Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175。

数：34 の節。そのうち 11 は移しで証明済み（T1c、T2b、T2b1、T2c、T2c1、S2、S3、S4、S8、S10、S11 の EXT-ETA）。

**いちばん弱い 3 つのつなぎ**（それが崩れたら崩れるものの多さと、確かめの少なさで選んだ）：L1 = S3、S4。L2 = T1c と S10。L3 = T2、T2b、T2b1、T2c。監査はそこに致命的な点も
進行を止める点も見つけなかった。その細かい点と、その査読者の細かい点は [SHIFT7-ja.md](SHIFT7-ja.md) §3.1 にある。鎖が使うのに補題として書かれていないただ 1 つのものは、η のずれが
$`[\psi_{\Omega_2}(\Omega_2), P')`$ にあるときの LONG-RS$`^U`$（R-1）：材料はどれもあり、段 1 で（S1、S2、T1b、だから下の半分が）と段 2 で（T2b1 が）使う。
今はそれは書かれた（行 T2b2）。

**33 回目に閉じた残り**（[SHIFT8-ja.md](SHIFT8-ja.md) §1.2。どれも査読 1 回で、致命的な点も進行を止める点も無い）：

- R-1：CAP-SUPPLY とあわせた LONG-RS$`^{\mathrm{rel}}`$。査読者の 1 行の直し 2 つのあとで、FRAG のもとで証明済み（XA$`^p`$ の上限は、やり直しでない動かない点の
  $`\mathrm{lh}(x)`$ も超えること。$`\pi`$ の符号のやり直しでは $`c = D' + 1`$ と取ること）。
- R-2 と L3-b：複写の無い基での計算の等式（2.6′）と TC⁺$`^{\mathrm{rel}}`$。移しで証明済み。引用は直した。
- L2-a、L1-b、L2-b：段 2 での確かめの行。移しで証明済み（査読者は行の見本を確かめた）。
- L1-a：可算の定数つきの $`\theta`$ より先の CNST$`_j`$。確かめた（失敗 0。査読者が新しい種で確かめ直した）。R-3 はもう表で直してある。
- 34 回目に、長いやり直しの段階のどの使い方も、この 2 つの直しを入れた LONG-RS$`^{\mathrm{rel}}`$ を引くようになった。裸の蓋でない基の点でも同じ。その査読者が
  場合を確かめた（[SHIFT8-ja.md](SHIFT8-ja.md) §2.1。査読 2 回）。
- 残り：2 つの段をまたぐ $`m^*`$ での越え方には確かめの行が無い（節目では使わない）。

**40 回目の表**（[SHIFT10-ja.md](SHIFT10-ja.md) §3.2。2 つ目の確かめに、その査読者とそこの §3.1 の査読者の直しを入れたもの）：

| 結果 | 40 回目のあとの状態 |
|---|---|
| $`X_9`$、$`X_{11}`$、$`X_{12}`$、$`X_{13}`$、$`X_{14}`$ | 成り立つ（影響を受ける符号でのちょうどの長い値を使わない） |
| $`X_{15}`$ から $`X_{18}`$ | 成り立つ（指数は $`G_2`$ より下） |
| $`X_{19}^\flat`$、$`X_{19}^{\mathrm{lin}}`$ | 証明済み（新しい。$`X_{19}^{\mathrm{lin}}`$ はそこの §3.1 とあわせて査読 2 回） |
| $`X_{19}`$、$`X_{20}`$、$`X_{21}`$ | 直した原子でもう一度証明済み（そこの §3.1。直しについて査読 1 回） |
| $`X_{22}`$、$`X_{23}`$ | 書いたままでは証明されていない |
| $`P'`$ より下の CAP-0、not-LOW、CAP-1、LONG-CLASS$`^\omega`$、NU-LOW″⁺、$`\nu_C \ge L(\omega+1)`$ | 書いたままでは証明されていない |
| CROSS-LIM、(C1)–(C3)、TC⁺$`^\omega`$、EMB、ONTO-FIN、PAIR、UP、NU、NU-NAME、LOW$`^\infty`$、$`\nu_C = \nu_S = L(\omega+1)`$、$`[0, \nu_C]`$ での主張 | 書いたままでは証明されていない |
| LC-STRICT（符号の不等式）、判定 SHIFT、核の半分 $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$、移しの補題 | 成り立つ |
| $`\nu_C`$ より上の $`Z^\Lambda`$ までの最前線（[SHIFT7-ja.md](SHIFT7-ja.md) §3.2 から [SHIFT10-ja.md](SHIFT10-ja.md) §1）と、$`R_2^S`$ での $`[0, Z^\varepsilon)`$ | 書いたままでは証明されていない |
| $`m_0 \ge \Omega_1`$ でのちょうどの長い式と、$`2 \le D \lt \hat G`$ での着地 | 書いたとおりでは偽（上からの評価は成り立つ） |
| [SHIFT2-ja.md](SHIFT2-ja.md) §3.1 の下からの評価の段階 (b)、NO-READL の段階 (b)（[SHIFT5-ja.md](SHIFT5-ja.md) §2.1） | 証明のとおりでは誤り。のちの定理はどれもそれを要らない |

**41 回目の表**（[SHIFT11-ja.md](SHIFT11-ja.md) §1.1、§1.2。回数を書いていなければ査読 1 回）：

| 結果 | 41 回目のあとの状態 |
|---|---|
| ENUM-REACH：段 1 と 2 の $`P'`$ より下のどの符号 $`m`$ でも $`r(\lambda) = k_\lambda(\Theta_\lambda(m))`$（S1、S2 に代わる） | 証明済み、FRAG のもと |
| COUNT♯、LAND$`^{\omega\sharp}`$、NEST、SHADOW-PREFIX、BOUND♯、CAP♯、CROSS♯、MONO♯ | 証明済み（数え上げは FRAG 無し） |
| TRANSLATION$`^{(3)}`$（$`G(\hat\zeta_3)`$ より下のどの符号でも） | 移しで証明済み、FRAG のもと |
| $`P'`$ より下の CAP-0、not-LOW、CAP-1、LONG-CLASS$`^\Omega`$、NU-LOW″⁺、$`\nu_C \ge L(\omega+1)`$（T1、T1b、T1c） | 移しで証明済み、FRAG のもと |
| CROSS-LIM、またいだ符号での (H4) と CAP-SUPPLY、(C1)–(C3)、TC⁺$`^\omega`$（符号を上げる写像の (EQ) は ENUM-REACH のあとで証明）、EMB、ONTO-FIN、PAIR、UP、NU（T2、T2b、T2b1、T2c） | 移しで証明済み、FRAG のもと |
| T0：$`\nu_C = \nu_S = L(\omega+1)`$、$`[0, \nu_C]`$ での主張。NU-NAME、LOW$`^\infty`$ | 証明済み、FRAG のもと |
| $`X_{22}`$、$`X_{23}`$ | $`\nu_C`$ より下なので T0 が覆う |
| $`X_9`$ から $`X_{18}`$、$`X_{19}^\flat`$、$`X_{19}^{\mathrm{lin}}`$。$`X_{19}`$ から $`X_{21}`$ | 書いたままで成り立つ。FAR-PIN$`^{L\sharp}`$ と EXP-BOUND で成り立つ（監査がもう一度読んだ） |
| LB-b-FALSE、NO-CROSS$`^F`$、TRANSLATION$`^e`$、TC⁺♯、EXP-BOUND | 証明済み（EXP-BOUND：$`\hat\zeta_H`$ の標準形は確かめ） |
| EXACT-LONG$`^e`$（[SHIFT6-ja.md](SHIFT6-ja.md) §1.2） | その範囲のどの符号でも偽 |
| NO-READL（[SHIFT5-ja.md](SHIFT5-ja.md) §2.1） | 書いたままでは証明されていない |
| $`\nu_C`$ より上の $`Z^\Lambda`$ までの最前線と、$`R_2^S`$ での $`[0, Z^\varepsilon)`$ | 書いたままでは証明されていない（区間の計算はやり直していない） |


**42 回目の表**（[SHIFT11-ja.md](SHIFT11-ja.md) §2.1、§2.2。どの結果も査読 1 回）：

| 結果 | 42 回目のあとの状態 |
|---|---|
| EQ$`^{\mathrm{all}}`$：直した値は、定数を上げるものも含めて BC$`^\pi`$ の類のどの基の取りかえとも入れかわる（ENUM-REACH の査読の m1 を閉じる。T2c は今はこれを引く） | 証明済み、FRAG のもと |
| T0：$`\nu_C = \nu_S = L(\omega+1)`$、$`[0, \nu_C]`$ での主張 | 証明済み、FRAG のもと（鎖は書いたままで完全） |
| VAL-IF：$`\nu_C`$ より上では段 1 か 2 の届く先は V0–V4 を通してだけ入る | 証明済み、読みで |
| 区域の条件 (REG♯) つきの GAP-CALC$`^{\sharp\mathrm{reg}}`$ | 移しで証明済み、FRAG のもと |
| FAR-PIN″♯、CROSS-LIM″♯、PAIR$`_j`$♯、LOW$`_j`$♯、C-TRANSFER♯、TC⁺″♯、TRANS-K″♯ | 移しで証明済み、FRAG のもと |
| 定理 C$`^{\Lambda\sharp}`$。$`R_2^C`$ で $`[0, Z^\Lambda]`$ での主張、$`\beta_0 \gt Z^\Lambda`$、その制限として最前線 $`X_A`$ から $`Z^\varepsilon`$ | 移しで証明済み、FRAG のもと |
| $`Z^\Lambda`$ より下のやり直し $`b = L(\lambda'')`$ で $`r(b) = k''_b(o_b(c''))`$ | 証明済み |
| $`Z^{\mathrm{LL}}`$（定理 C$`^{\mathrm{LL}}`$） | 証明されていない（FALSE-LB″ は予想） |
| $`\beta_0 \gt \nu_C`$。$`R_2^S`$ で $`[0, \nu_C]`$ と $`[0, F_\nu)`$ での主張 | 証明済み、FRAG と EQ$`^{\mathrm{all}}`$ のもと（査読の進行を止める点 B-1 はこの書き方） |
| 定理 X-COF、補題 E1$`^p`$ | 証明済み、FRAG 無し（許される基について） |
| UNIFORM-B、FIN-CROSS、K2$`^{\mathrm{cap}}`$ | その仮定のもとで証明済み（K2$`^{\mathrm{cap}}`$ は m1 の直しのあと） |
| やり直しに沿った $`R_2^S`$ での $`[0, Z^\varepsilon)`$ | 概略 |
| $`R_2^S`$ での $`[0, Z^\Lambda)`$。$`R_2^C`$ での $`[0, Q^\Lambda]`$ | 条件つき（書き方だけ確かめた） |

**43 回目の表**（[SHIFT11-ja.md](SHIFT11-ja.md) §3.1、§3.2。回数を書いていなければ査読 1 回）：

| 結果 | 43 回目のあとの状態 |
|---|---|
| READ$`^{\mathrm{FP}}`$、RANGE″（$`Z^{\mathrm{FP}}`$ より下で段 3 の長いやり直しはまたがれない）。NEST″、COUNT♯″、LAND″♯、SHADOW-PREFIX″ | 証明済み、FRAG 無し |
| ENUM-REACH″$`^{\mathrm{FP}}`$：$`Z^{\mathrm{FP}}`$ より下のどのやり直し $`b = L(\lambda'')`$ でも長い符号も含めて $`r(b) = k''_b(o_b(c''))`$（[SHIFT10-ja.md](SHIFT10-ja.md) §2.1 の F-1 を閉じる） | 移しで証明済み、FRAG のもと（査読の m1 つき） |
| EQ″ | 遠い移しについて証明済み。ほかの写像では書いたままでは証明されていない（使わない） |
| FALSE-LB″ | 証明済み、FRAG のもと |
| LB″、EXACT-LONG-CL″\*（[SHIFT10-ja.md](SHIFT10-ja.md) §1.1）。LB″$`^G`$、強い CROSS″、CROSS-O″、EXACT-LONG″$`^G`$、EXACT-F″、AGREE″ の値（そこの §2.1） | 直した値が違う所で偽。取り下げ |
| 定理 C$`^{\mathrm{LL}\sharp}`$、C$`^{\mathrm{FP}\sharp}`$。$`R_2^C`$ で $`[0, Z^{\mathrm{FP}}]`$ での主張、$`\beta_0 \gt Z^{\mathrm{FP}}`$。その制限として $`Z^{\mathrm{LL}}`$、$`L(\theta'_2\cdot\Omega_1)`$、$`L(\theta'_2\cdot\Omega_2)`$ | 移しで証明済み、FRAG のもと |
| 定理 Z$`^{\mathrm{LG}}`$：蓋だけで $`\beta_0 \gt Z^{\mathrm{LG}}`$ と $`R_2^C`$ で $`[0, Z^{\mathrm{LG}}]`$ での主張（SKEL″$`^{\mathrm{cr}}`$、UPPER$`^{\mathrm{cr}}`$、PRED1$`^{\mathrm{cr}}`$、C$`^{\Lambda 1}`$） | 移しで証明済み、FRAG のもと。§3.1 とあわせ $`(Z^\Lambda, Z^{\mathrm{LG}}]`$ は査読 2 回 |
| $`R_2^S`$ で $`[0, Z^\Lambda)`$ での主張。BLOCK″$`_0(Z^\Lambda)`$♯、$`\beta_0 \gt Q^\Lambda`$ | 証明済み、FRAG のもと（前は条件つき） |
| UNIFORM-B⁺、直した K2$`^{\mathrm{cap}}`$ | その仮定のもとで証明済み |
| S-COND | 含意として証明済み。$`R_2^S`$ で $`[0, Z^{\mathrm{LG}})`$ での主張は LONG″-CAP のもとでの条件つき |
| $`Z^{\mathrm{FP}}`$ より下の CAP-0″（鋭い形） | 証明済み、FRAG のもと |
| LOW-RED″、BASE″、NU-LOW‴、SHIFT$`_3'`$（$`L_3(\omega) \lt_2 L_3(\omega+1)`$） | 含意として証明済み |
| $`T_3^S \le \nu_3`$、$`T_3^S = \nu_3`$ | 証明されていない（査読の進行を止める点 B-1） |
| $`Z^{\mathrm{FP}}`$ での $`R_2^S`$。NU-CT$`_3`$ | 概略 |

**44 回目の表**（[SHIFT12-ja.md](SHIFT12-ja.md) §1.1、§1.2。回数を書いていなければ査読 1 回）：

| 結果 | 44 回目のあとの状態 |
|---|---|
| TIER、THETA″$`^W`$（$`x \lt \omega^2`$ の段 $`G''(\Omega_2+x)`$ をやり直しの窓の中で読む）。$`Z^{\mathrm{W}}`$ までの範囲の補題（段 3 の長いやり直しはまたがれない） | 証明済み、FRAG 無し |
| ENUM-REACH″$`^{\mathrm{W}}`$：$`Z^{\mathrm{W}}`$ より下のどのやり直し $`b = L(\lambda'')`$ でも $`r(b) = k''_b(o_b(c''))`$。$`\hat G''`$ 以上の符号は $`F''_b`$ に着地 | 移しで証明済み、FRAG のもと |
| 定理 C$`^{\mathrm{W}\sharp}`$。$`R_2^C`$ で $`[0, Z^{\mathrm{W}}]`$ での主張、$`\beta_0 \gt Z^{\mathrm{W}}`$。その制限として点 $`L(\theta'_2\cdot(\Omega_2+x))`$ | 移しで証明済み、FRAG のもと |
| $`Z^{\mathrm{W}}`$ より下の CAP-0″（鋭い形）。留めの集合を広げた遠い頂上の補題（43 回目の査読の m1） | 証明済み、FRAG のもと |
| TAUL | 証明済み、FRAG 無し |
| SKEL″$`^\nu`$（$`\le_1`$ の前の点がどうであっても $`y_3`$ より下での段 3 の区域の骨組み） | $`\min(y_3, L(\Omega_\omega))`$ より下で移しで証明済み、FRAG のもと。その上は含意 |
| SHIFT$`_3''`$：(Y)、(H2$`^{\mathrm{cr}}`$)、(H3) から、3 重の入れ子つきで $`L_3(\omega) \lt_2 \nu_3`$、$`T_3^S = y_3 = \nu_3`$（43 回目の B-1 を閉じる） | 含意として証明済み、FRAG のもと |
| 43 回目の査読の仮定つきの NU-LOW‴ | 含意として証明済み |
| $`\nu_3`$。$`[Z^{\mathrm{W}}, L(\Omega_\omega))`$ での CAP-0″、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$)、1 つ上の LEFT⁺ | 未解決 |
| (H3)、NU-CT$`_3`$。2 つ目の窓。$`Z^{\mathrm{W}}`$ での $`R_2^S`$ | 概略 |
| 符号 $`G''(\theta'_3\cdot\omega^2)`$ での段 3 の長いやり直しの最初のまたぎ | 予想 |
| $`r(Z^\Lambda) = \delta''_1(L(\theta'_2\cdot\omega^2+\omega^2)) + 1`$。LONG″-CAP（43 回目の予想） | 証明済み、FRAG のもと |
| LOC-PASS | 証明済み |
| S-PAST-Λ：$`R_2^S`$ で $`[0, Z^{\mathrm{LG}})`$ での主張 | 証明済み、FRAG のもと |
| S-FOLLOW。$`R_2^S`$ で $`[0, Z^{\mathrm{FP}})`$ での主張と、$`Z^{\mathrm{FP}}`$ より下の Carlson の判定 | 証明済み、FRAG のもと |
| 基 $`Z^{\mathrm{FP}}`$ で蓋だけを読む帰納法：$`\beta_0 \gt Z^{\mathrm{FPG}}`$、$`R_2^C`$ で $`[0, Z^{\mathrm{FPG}}]`$ での主張 | 移しで証明済み、FRAG のもと。C$`^{\mathrm{W}\sharp}`$ の行とあわせ $`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$ は査読 2 回 |
| S-COND$`^{\mathrm{FP}}`$ | 含意として証明済み |
| 注意「$`Z^{\mathrm{FP}}`$ が $`R_2^S`$ の芯に入るのは、分解できない $`\mu`$ が $`(r(Z^{\mathrm{FP}}), \beta_0]`$ にあるとき、またそのときに限る」 | 「のとき」の半分だけ証明済み |
| CAP$`^{\mathrm{FP}}`$（$`r(Z^{\mathrm{FP}})`$ の蓋） | 予想 |

**45 回目の表**（[SHIFT12-ja.md](SHIFT12-ja.md) §2.1、§2.2。回数を書いていなければ査読 1 回。$`\lambda_{\mathrm{FP}}`$ と $`\lambda_{\mathrm{W}}`$ は $`Z^{\mathrm{FP}}`$ と $`Z^{\mathrm{W}}`$ の添字）：

| 結果 | 45 回目のあとの状態 |
|---|---|
| $`x \lt G''(\Omega_2\cdot 2)`$ での段 $`G''(\Omega_2+x)`$ を 2 つ目の窓 $`[F''_b, L(\lambda''+\Omega_1\cdot 2))`$ で読む。$`L`$ の添字は $`[\theta'_2\cdot(\Omega_2+G''(\Omega_2\cdot 2)), \theta'_2\cdot\Omega_2\cdot 2)`$ に無い | FRAG 無しで証明済み |
| 2 つ目の窓の上の遠い留め（運び、留め、頂上の補題、長いやり直しの一歩、またぎの補題） | 移しで証明済み、FRAG のもと |
| ENUM-REACH″$`^{\mathrm{W2}}`$：$`Z^{\mathrm{W2}}`$ より下のどのやり直しでも $`r(b) = k''_b(o_b(c''))`$。またがれるやり直しはどれも短い。$`r(Z^{\mathrm{W}}) = \delta''_1(L(\theta'_2\cdot(\Omega_2+\omega^2)+\Omega_1+\omega^2)) + 1`$ | 移しで証明済み、FRAG のもと |
| 定理 C$`^{\mathrm{W2}\sharp}`$。$`R_2^C`$ で $`[0, Z^{\mathrm{W2}}]`$ での主張、$`\beta_0 \gt Z^{\mathrm{W2}}`$ | 移しで証明済み、FRAG のもと |
| $`\Omega_2^2`$ より下の読み $`o_b(G''(\Omega_2\cdot\xi+x)) = L(\lambda''+\Omega_1\cdot o_b(\xi)+o_b(x))`$。$`R_2^C`$ で $`[0, Z^{\mathrm{WW}}]`$ での主張、$`\beta_0 \gt Z^{\mathrm{WW}}`$ | 移しで証明済み、FRAG のもと（査読は一番弱い段階を確かめた） |
| 鋭い形の $`Z^{\mathrm{WW}}`$ より下の CAP-0″ | 証明済み、FRAG のもと |
| 段 3 の長いやり直しの最初のまたぎが符号 $`G''(\theta'_3\cdot\omega^2)`$ で起こること | 予想 |
| CAP$`^{\mathrm{FP}}`$：$`r(Z^{\mathrm{FP}})`$ と $`L(\lambda_{\mathrm{FP}} + G''(\omega^2)\cdot k)`$ の届く先 | 証明済み、FRAG のもと |
| S-F2：$`R_2^S`$ で $`[0, Z^{\mathrm{W}})`$ での主張、$`Z^{\mathrm{W}}`$ より下の Carlson の判定 | 証明済み、FRAG のもと |
| S-FPG：蓋による $`R_2^S`$ で $`[0, Z^{\mathrm{FPG}})`$ での主張 | 証明済み、FRAG のもと。S-F2 とあわせ $`[0, Z^{\mathrm{FPG}})`$ は査読 2 回 |
| BASE-TEST″ と $`(Z^{\mathrm{FP}}, Z^{\mathrm{W}}]`$ の基の点の表 | 証明済み。ただし $`Z^{\mathrm{W}}`$ の行は除く |
| 基 $`Z^{\mathrm{W}}`$ で蓋だけを読む帰納法：$`\beta_0 \gt Z^{\mathrm{WG}}`$、$`R_2^C`$ で $`[0, Z^{\mathrm{WG}}]`$ での主張 | 移しで証明済み、FRAG のもと。ENUM-REACH″$`^{\mathrm{W2}}`$ とあわせ $`(Z^{\mathrm{W}}, Z^{\mathrm{WG}}]`$ は査読 2 回 |
| S-COND$`^{\mathrm{W}}`$ | 含意として証明済み |
| $`R_2^S`$ の論文で証明したとする LB$`^{\mathrm{W}}`$ | 未証明（進行を止める点 B-1）。$`r(Z^{\mathrm{W}})`$ の値は ENUM-REACH″$`^{\mathrm{W2}}`$ から出る |
| $`r(Z^{\mathrm{W}})`$ と S-COND$`^{\mathrm{W}}`$ からの $`R_2^S`$ で $`[0, L(\lambda_{\mathrm{W}} + G''(\omega^2)))`$ での主張 | 組み合わせは査読されていない。数えない |
| CAP$`^{\mathrm{W}}`$ (ii) | 予想 |
| $`\nu_3`$。1 つ上の LEFT⁺、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$) | 未解決 |

**のちに（46 回目）：** LB$`^{\mathrm{W}}`$ と CAP$`^{\mathrm{W}}`$ (ii) は証明され、上の組み合わせは査読された証明に置き換わった（次の表）。

**46 回目の表**（[SHIFT12-ja.md](SHIFT12-ja.md) §3.1、§3.2。回数を書いていなければ査読 1 回。乗数とは $`\zeta \lt \psi_{\Omega_3}(0)`$）：

| 結果 | 46 回目のあとの状態 |
|---|---|
| 全部書き出した $`(Z^{\mathrm{W2}}, Z^{\mathrm{WW}}]`$ の段階（$`\lambda''+\Omega_1\cdot u`$ での $`L`$ の定義域、$`\Omega_2^2`$ より下の読み、符号 $`\Omega_1+c`$ のつなぎ） | FRAG 無しで証明済み（つなぎは FRAG のもと）。この回に全部を、45 回目に一番弱い段階を読まれた |
| THETA″$`^{\mathrm{V}}`$：どの正規な乗数でも段の補題と読み $`o_b(G''(\zeta)) = L(\lambda''+1+R''_b(\zeta))`$ | FRAG 無しで証明済み |
| 符号 $`\Omega_1\cdot m+d`$ のつなぎ（和だけ）と、$`\psi_{\Omega_2}(0)`$ までのどのヴェブレンの符号のつなぎ | 証明済み。2 つ目は FRAG のもと |
| しきい値 $`\psi_{\Omega_2}(0)`$ の遠い留め。$`Z^{\mathrm{V}}`$ より下の ENUM-REACH″$`^{\mathrm{V}}`$ | 移しで証明済み、FRAG のもと |
| 定理 C$`^{\mathrm{V}\sharp}`$。$`R_2^C`$ で $`[0, Z^{\mathrm{V}}]`$ での主張、$`\beta_0 \gt Z^{\mathrm{V}}`$ | 移しで証明済み、FRAG のもと。$`(Z^{\mathrm{WW}}, L(\theta'_2\cdot\Omega_2^\omega)]`$ は和だけのつなぎを使う |
| 鋭い形の $`Z^{\mathrm{V}}`$ より下の CAP-0″。$`Z^{\mathrm{V}}`$ より下で長いやり直しはまたがれない。$`r(Z^{\mathrm{V}})`$ | 証明済み、FRAG のもと |
| $`\psi_{\Omega_3}`$ の原子を持つ乗数 | 未解決 |
| $`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_3))`$ までの主張。段 3 の長いやり直しの最初のまたぎが符号 $`G''(\theta'_3\cdot\omega^2)`$ で起こること | 予想 |
| CAP$`^{\mathrm{W}}`$ と LB$`^{\mathrm{W}}`$（B-1 を閉じる） | 証明済み、FRAG のもと |
| $`R_2^S`$ で $`[0, Z^{\mathrm{WG}})`$、$`[0, Z^{\mathrm{W2}})`$、$`[0, Z^{\mathrm{WW}})`$ での主張。$`Z^{\mathrm{WW}}`$ より下の Carlson の判定 | 証明済み、FRAG のもと。S-F2 とあわせ $`[0, Z^{\mathrm{W}})`$ は査読 2 回 |
| BASE-TEST″ と $`(Z^{\mathrm{W}}, Z^{\mathrm{WW}}]`$ の基の点の表 | 証明済み |
| 基 $`Z^{\mathrm{W2}}`$ と $`Z^{\mathrm{WW}}`$ で蓋だけを読む帰納法：$`\beta_0 \gt Z^{\mathrm{WWG}}`$、$`R_2^C`$ で $`[0, Z^{\mathrm{WWG}}]`$ での主張 | 移しで証明済み、FRAG のもと。C$`^{\mathrm{V}\sharp}`$ とあわせ $`(Z^{\mathrm{WW}}, Z^{\mathrm{WWG}}]`$ は査読 2 回 |
| CAP$`^{\mathrm{W2}}`$：$`r(Z^{\mathrm{W2}})`$ | 証明済み、FRAG のもと |
| CAP$`^{\mathrm{WW}}`$。そこからの $`R_2^S`$ で $`Z^{\mathrm{WW}}`$ を越える主張 | 予想（その値 (i) は ENUM-REACH″$`^{\mathrm{V}}`$ の 1 行）。組み合わせは査読されていない。数えない |
| $`\nu_3`$。1 つ上の LEFT⁺、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$) | 未解決 |

**のちに（47 回目）：** 上の行 $`r(Z^{\mathrm{V}})`$ は、そこでの証明のままでは条件つき（証明が $`Z^{\mathrm{V}}`$ より上の届く先、つまり帰納法の範囲の外を読む。
[SHIFT13-ja.md](SHIFT13-ja.md) §1.2 の査読の B-1）。値は ENUM-REACH″$`^\theta`$ でもう一度証明された。CAP$`^{\mathrm{WW}}`$ は証明された（次の表）。

**47 回目の表**（[SHIFT13-ja.md](SHIFT13-ja.md) §1.1、§1.2。回数を書いていなければ査読 1 回。乗数とは $`\zeta \lt \theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$、$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$）：

| 結果 | 47 回目のあとの状態 |
|---|---|
| どの添字でもの DOWN″、CMAX、$`L`$ の定義域の判定（46 回目の査読の m1） | FRAG 無しで証明済み |
| THETA″$`^\theta`$：どの正規な乗数でも段の補題と、$`\theta`$ より下のずれの上への読み $`o_b(G''(\zeta)) = L(\lambda''+1+R''_b(\zeta))`$ | FRAG 無しで証明済み |
| EXACT-GS⁺ | FRAG 無しで証明済み |
| $`\theta`$ より下のどの符号のつなぎ。しきい値 $`\theta`$ の遠い留め（端の点 $`L(\lambda''+\theta)`$ より下） | 証明済み、FRAG のもと |
| $`Z^\theta`$ より下の ENUM-REACH″$`^\theta`$、$`r(Z^{\mathrm{V}})`$ と $`r(Z^\Phi)`$ つき | 移しで証明済み、FRAG のもと |
| 定理 C$`^{\theta\sharp}`$。$`R_2^C`$ で $`[0, Z^\theta]`$ での主張、$`\beta_0 \gt Z^\theta`$、$`T_3^C \gt Z^\theta`$ | 移しで証明済み、FRAG のもと。$`(Z^{\mathrm{V}}, Z^\Phi]`$ は $`\Gamma`$ の原子の層だけを使い、$`(Z^\Phi, Z^{\mathrm{E}}]`$ は EXACT-GS⁺ も使う |
| 鋭い形の $`Z^\theta`$ より下の CAP-0″。$`Z^\theta`$ より下で長いやり直しはまたがれない | 証明済み、FRAG のもと |
| PLATEAU″-3、ALIGN″、HN″、MONO″（定数無し）。含意としての LONG-FIRST″ | 証明済み |
| THETA″$`^{\mathrm{READ}}`$。$`L(\theta'_2\cdot\theta'_2)`$ までの主張 | 予想 |
| $`[\theta, P')`$ の符号のつなぎでの留め。$`r(Z^\theta)`$ | 未解決 |
| CAP$`^{\mathrm{WW}}`$：$`r(Z^{\mathrm{WW}})`$、$`r(Z^{\mathrm{WWG}})`$ とその間のやり直し | 証明済み、FRAG のもと |
| $`R_2^S`$ で $`[0, Z^{\mathrm{WWG}})`$、$`[0, L(\theta'_2\cdot\Omega_2^\omega))`$、$`[0, Z^{\mathrm{V}})`$ での主張。$`Z^{\mathrm{V}}`$ より下の Carlson の判定 | 証明済み、FRAG のもと。$`[0, Z^{\mathrm{WW}})`$ は査読 2 回 |
| BASE-TEST″$`^{\mathrm{V}}`$、NEXT-BASE″$`^{\mathrm{V}}`$ と $`(Z^{\mathrm{WW}}, Z^{\mathrm{V}})`$ の基の点の表 | 証明済み |
| 基 $`Z^{\mathrm{V}}`$ で蓋だけを読む帰納法：$`\beta_0 \gt Z^{\mathrm{VG}}`$、$`R_2^C`$ で $`[0, Z^{\mathrm{VG}}]`$ での主張 | 移しで証明済み、FRAG のもと。C$`^{\theta\sharp}`$ とあわせ $`(Z^{\mathrm{V}}, Z^{\mathrm{VG}}]`$ は査読 2 回 |
| $`R_2^S`$ で $`[0, L(\lambda_{\mathrm{V}}+G''(\omega^2)))`$ での主張、$`Z^{\mathrm{V}} \in \mathrm{Core}(R_2^S)`$ | 証明されていない（進行を止める点 B-1：帰納法の範囲の外から $`r(Z^{\mathrm{V}})`$ を使った）。ENUM-REACH″$`^\theta`$ との組み合わせは査読されていない。数えない |
| CAP$`^{\mathrm{V}}`$ (ii) | 予想 |
| $`\nu_3`$。1 つ上の LEFT⁺、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$) | 未解決 |
