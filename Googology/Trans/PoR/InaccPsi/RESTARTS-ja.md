[← Back](README-ja.md) | [English](RESTARTS.md) | [Japanese](RESTARTS-ja.md)

# $`\upsilon_{\omega^3}`$ より上の $`R_2^+`$：補題 FRAG、$`\le_2`$ を保つ基の付け替え、やり直しのブロック

このページは [README-ja.md](README-ja.md) の §3 の続き。状態の言葉はそこと同じ：**証明済み**は、独立した査読者が、
致命的な点も止める点も無く証明済みと判定したもの。このページの結果はどれも 2026-10 のもので、回数を書いていなければ
**査読 1 回**。**概略**と書いたものは、査読者が「証明済み（概略）、反証されず」と判定したもの。証明済みには数えない。$`\Xi_\omega`$ より上の結果（正確な届く先、骨組みの終わり、長さ 3 の最小の鎖）は
3 ページ目 [REACHES-ja.md](REACHES-ja.md) にある。

**記号。** $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$。点 $`\alpha`$ の届く先を $`\mathrm{lh}(\alpha) = \max\{\gamma : \alpha \le_1 \gamma\}`$ と書く。
やり直しの添字とは、$`\omega^2`$ の 0 でない倍数 $`\lambda`$ のこと。$`\lambda = \lambda_0 + \omega^e`$（カントール標準形の最後の項、
$`e \ge 2`$）と書き、$`c(\lambda) = -1 + e`$ をずれと呼ぶ（$`e`$ が有限なら $`e - 1`$、無限なら $`e`$）。やり直しの点は
$`\rho_\lambda = \upsilon_\lambda`$。その上の組は $`\tau^\lambda_j = \upsilon_{\lambda+\omega j}`$ と $`\delta^\lambda_j = \upsilon_{\lambda+\omega j+1}`$（$`j \ge 1`$）。
$`\delta_\lambda = \delta^\lambda_1`$ は最初のブロックの上端。$`\Xi_1 \lt \Xi_2 \lt \cdots`$ は $`\iota \mapsto \upsilon_\iota`$ の 0 でない不動点で、
$`\Xi_\omega = \sup_n \Xi_n`$。$`\lambda \lt \Xi_\omega`$ では $`c^*(\lambda) = c(\lambda)`$、$`c^*(\Xi_\omega) = \Xi_\omega + 1`$ とおく。

## 1. 補題 FRAG（証明済み）

**定理 FRAG**（有限の形）。$`\kappa`$ を $`\varepsilon`$ 数である $`\upsilon`$ の点とし、$`b_1 \lt \cdots \lt b_m`$ と
$`c_1 \lt \cdots \lt c_m`$ を $`\kappa`$ より上の $`\upsilon`$ の点とする。$`\kappa`$ 未満か $`b_k`$ の区間（そのパラメータも含む）にある
順序数の有限集合 $`F`$ のどれにも、$`F`$ の上の写像 $`\Psi`$ があって：$`\kappa`$ より下では恒等、$`b_k`$ を $`c_k`$ に、$`b_k`$ の
区間を $`c_k`$ の区間に送り、$`R_1^+`$ の $`0, +, \le, \le_1`$ を両向きに保ち、$`\upsilon`$ の点を $`\upsilon`$ の点に、それ以外を
それ以外に送る。

証明の流れ。各 $`b_k`$ の上の区間を、Wilken の基の付け替え $`\pi_{\beta_k, b_k}`$ で $`(\beta_k, \beta_k^+)`$ に押し下げる。
ここで $`\beta_k`$ は $`b_{k-1}`$ の区間の中の $`\varepsilon`$ 数（補題 COMP）。その区間の中では、古いパラメータは普通の部分項に
なる（Wilken, APAL 145 (2007) 130–161, Lemma 6.10）。$`m-1`$ 回の後、すべては $`b_1`$ の区間に入る。1 回の基の付け替えで
$`c_1`$ に動かす。そのあと $`c_k`$ の側で各段を元に戻す。どの段も $`\lt, +, \le_1`$ を両向きに保つ（補題 ST。Wilken, APAL 145
(2007) 162–175 の Cor 5.7、Lemma 4.4、Thm 5.3 から）。要の点（査読者が確かめた）：その論文の §4 は $`\{1\} \cup E`$ のどの
基も許すので、これらの結果は $`\upsilon`$ の点でない基 $`\beta_k`$ でも成り立つ。補題 R：閉包の集合は有限。$`\le_1`$ の部分は
すべての種類の組（場合 D1–D4）を扱う。

$`V_3`$ より下の順序の証明（[R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md)）の前の査読は、FRAG を見取り図としてだけ
認めた。その見取り図は、読んで確かめただけの補題を使っていた。新しい証明はそれを使わない。査読者は引用をすべて
論文の本文と照らし、すべての場合を確かめた：致命的な点も止める点も無し。言い回しの指摘が 5 つ。

**補題 RS と RS$`^h`$。** どの $`h \ge 1`$ でも、$`R_2^S`$ で $`\rho_h \le_1 \delta^h_1 + 1`$。ここで $`\rho_h = \upsilon_{\omega^2 h}`$
（証明済み。前に査読済みのブロックの結果を使う）。だから $`\mathrm{lh}(\rho_h) = \delta^h_1 + 1`$。

**これで成り立つこと。** 「FRAG を仮定すれば証明済み」だった結果は、すべて証明済みになる：

- 定理 B′′ の全体と、すべての組での定理 EQB′′：$`\upsilon_{\omega^3}`$ より下で $`R_2^C = R_2^S`$。
- $`V_3 = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0)`$ より下での定理 S：$`V_3`$ 未満のすべての標準形の行列で $`\Phi_3`$ は
  順序を保ち、$`\iota(\Phi_3(M)) = \mathcal{T}_3(M)`$（順序の証明は査読 1 回、FRAG は査読 1 回）。
- $`\upsilon_{\omega^3}`$ までの定理 CORE-S と、$`\beta_0 \ge \upsilon_{\omega^3}`$。
- 前の査読の小さな指摘 6 つ：3 つは直した。1 つは補題 DIAG′ で済む。1 つは書き直した。1 つは不要になった。

確かめたこと（どれも 60 秒未満、失敗 0）：基が 1〜6 個の乱数の配置 20,239 個。順序と $`+`$ で 10,573,114 組。区間の中の
$`\le_1`$ で 836,413 組。わざと入れた 3 つのバグはすべて見つかった。査読者が新しい種で回したもの：約 190 万組、失敗 0。
これらは Wilken の項のプログラムのモデルを試すもので、$`R_1^+`$ そのものではない。

**予想**（確認済み、使わない）：証明の写像は $`\beta_k`$ の選び方によらない。

## 2. $`\le_2`$ を保つ基の付け替え（定理 FRAG2）

集合 $`Y`$ の上で $`R_2^+`$ が**骨組み型**とは：$`Y`$ の $`\upsilon`$ の点でない点はどれも $`R_1^+`$ の届く先を持ち、$`\lt_2`$ の組は
どれも $`(\upsilon_\xi, \upsilon_{\xi+1})`$ であること。$`\mathrm{cap}(u) = \mathrm{lh}(u)`$ と書く。

- **定理 FRAG2**（証明済み。FRAG を使う）。$`\Psi`$ を FRAG の写像、$`Y`$ を有限集合とし、$`Y \cup \Psi[Y]`$ の上で $`R_2^+`$ が
  骨組み型とする。このとき、$`\Psi`$ が $`Y`$ の上で $`0, +, \le, \le_1, \le_2`$ を保つ ⇔ $`Y`$ の $`\upsilon`$ の点 $`u`$ と $`Y`$ の
  $`z \gt u`$ のすべてで、(C1) $`z \le \mathrm{cap}(u) \Leftrightarrow \Psi z \le \mathrm{cap}(\Psi u)`$、(C2)
  $`u \lt_2 z \Leftrightarrow \Psi u \lt_2 \Psi z`$。つまり $`\le_2`$ を保つ写像は、添字だけでは決まらず、$`Y`$ から見える届く先と組の
  事実で決まる。系 FRAG2-D は $`\upsilon_{\omega^3}`$ より下の定義域全体での添字の条件を与える。基が 1 つなら FRAG は要らない
  （系 FRAG2-1）。査読者の注：この定理は、$`R_1^+`$ の $`0, +, \le, \le_1`$ を保ち、$`\upsilon`$ の点を保ち、下の区間を固定する
  どの写像でも成り立つ。
- **補題 SK3**（証明済み、FRAG なし）。$`\upsilon_{\omega^3}`$ より下で、$`R_2^S`$ も $`R_2^C`$ も骨組み型。
- **NAIVE-FAIL**（証明済み）。$`+`$ の無い $`R_2`$ での Wilken の規則「極限の基を極限の基に動かす」（Wilken 2020, p. 434）は
  $`R_2^+`$ では偽：$`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ だが、$`\upsilon_{\omega^2}`$ には $`\lt_2`$ の後の元が無い。彼の縮める写像は $`+`$ を
  保たない。
- **補題 PAIR-SK**（$`R_2^S`$ で証明済み、FRAG なし）。$`\upsilon_\lambda \lt_2 \upsilon_{\lambda+1}`$ の十分条件。1 回の基の付け替えで示す。
- **$`\upsilon_{\omega^3}`$ より上**（$`R_2^S`$）。$`\delta_O = \upsilon_{\omega^3+\omega+1}`$ と書く。$`\upsilon_{\omega^3}`$ の最初のやり直しの
  ブロックと TOP$`^{\omega^3}`$（FRAG なし）。そして**定理 RS$`^{\omega^3}`$**：$`\mathrm{lh}(\upsilon_{\omega^3}) = \delta_O + 2`$。
  プログラムが出す届く先「ブロックの上端 + 2」がこれ。どれも証明済み。
- **系 6.4**（証明済み）。$`R_2^S`$ は $`\delta_O + 3`$ より下で骨組み型。$`R_2^S`$ が骨組み型でなくなる最初の点 $`\nu_S`$ は可算で、
  どの長さ 3 の鎖の上端以下。§3 により $`\upsilon_{\Xi_\omega+\omega^2}`$ 以上。

証明されていないこと：FRAG2 が §3 の補題 RS$`_\lambda`$ をどの $`\lambda`$ でも片付けるという注意（行き先のやり直しの選び方と、
動かしたずれを持つ行き先の cap が示されていない。RS$`_\lambda`$ そのものは別の道で証明済みになった、
[REACHES-ja.md](REACHES-ja.md) §1）。脇の注意「FRAG なしで、定義域全体の同型 ⇔ RS が成り立たない」
（「⇐」の向きは FRAG が要る。もう一度は確かめていない）。予想：**CAP**、$`\eta \ge 1`$ で
$`\mathrm{lh}(\upsilon_{\omega^2\eta}) = \upsilon_{\omega^2\eta+\omega+1} + (1 + \mathrm{logend}(\eta))`$（プログラムは 11 個のやり直しで一致。その中に
$`\upsilon_{\omega^\omega}`$ での「上端 + $`\omega`$」がある。[REACHES-ja.md](REACHES-ja.md) §1 の定理 OFF-V により、段 0 のすべての
やり直しで成り立ち、$`\Xi_\omega`$ で外れる）。**FRAG2-GEN**、骨組みの外では、FRAG2 は $`\upsilon`$ の点でない
$`\varepsilon`$ 数の基も、Wilken の $`\iota_{\tau,\alpha}`$ で動かす必要がある（一部は証明済み、[REACHES-ja.md](REACHES-ja.md) §4）。
$`\nu_S`$ の値は未解決。その上下の評価と、ありうる 2 つの種類は [REACHES-ja.md](REACHES-ja.md) §4 にある。

確かめたこと（失敗 0）：モデルで 4,144 個のパターンの上の 25,238 個の写像（C1 か C2 を外すと食い違う）。プログラム
`phi3def2` で、動かした標準形の行列 35,104 個と 5,384,652 組：$`\le_1`$ と $`\le_2`$ の事実は、FRAG2 が予言する所でちょうど変わる。
$`\upsilon_{\omega^3}`$ のブロックへ動かした 2,591 個のパターン：変化なし。査読者の新しい種での再実行（新しい行列 12,539 個、
1,595,592 組）：失敗 0。査読者の注：モデルの検査は証明をくり返すだけで、プログラムは独立した判定器ではない。

## 3. $`\Xi_\omega`$ までのやり直しのブロック（定理 BLK$`^\Xi`$）

**定理 BLK$`^\Xi`$**（証明済み。$`R_2^S`$ と $`R_2^C`$ の両方。FRAG なし）。$`\alpha \lt \upsilon_{\Xi_\omega+\omega^2}`$ のすべてで：

- (i) 左端が $`\upsilon_{\Xi_\omega+\omega^2}`$ 未満の $`\lt_2`$ の組は、ちょうど $`(\tau^\lambda_j, \delta^\lambda_j)`$。ここで $`\lambda`$ は 0 か
  やり直しの添字、$`j \ge 1`$。
- (ii) やり直しの点 $`\rho_\lambda`$（$`\lambda \le \Xi_\omega`$）には $`\lt_1`$ の前の元も $`\lt_2`$ の後の元も無く、
  $`[\rho_\lambda, \delta_\lambda] \subseteq \{\gamma : \rho_\lambda \le_1 \gamma\} \subseteq [\rho_\lambda, \delta_\lambda + c^*(\lambda)]`$。
- (iii) ほかの $`\alpha`$ は上端 $`d`$ のブロックに入り、$`\alpha \le_1 \gamma`$ となるのは、ちょうど $`R_1^+`$ で $`\alpha \le_1 \gamma`$ となる
  $`\gamma \le d`$。

(ii) の上の端は**補題 TOP$`_\lambda`$**（証明済み、両方の構造）。$`\lambda`$ のすぐ前のやり直しはずれが小さい、ということで
うまくいく。$`\upsilon_{\omega^3\cdot 2}`$ のような場合は、固定したパラメータを 1 つ足して扱う。$`\lambda = \omega^3`$ の場合が
TOP$`_3`$ で、$`R_2^C`$ の核の下界を止めていたもの。前のメモは、この議論では届く先「上端 + $`\omega`$」を抑えられないと言って
いたが、それは誤り（$`\omega`$ は固定したパラメータ）。**定理 EQB$`^\lambda`$**（証明済み）：$`[0, \upsilon_{\lambda+\omega^2})`$ で
$`R_2^C`$ と $`R_2^S`$ は一致する。例外になりうるのは組 $`(\rho_\mu, \delta_\mu + \xi)`$、$`0 \lt \xi \le c^*(\mu)`$ だけで、そこでは
$`S \Rightarrow C`$ が成り立つ。

**補題 RS$`_\lambda`$**（下の端、$`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^*(\lambda)`$）：最初の見取り図は証明されていなかった（行き先の
やり直しの選び方が $`e = e' + 1`$ のとき、例えば $`\lambda = \omega^4`$ でうまくいかない）。いまは $`\lambda \le \Xi_\omega`$ のすべてで、
$`R_2^S`$ でも $`R_2^C`$ でも、独立した 2 つの論文で**証明済み**（査読 2 回。[REACHES-ja.md](REACHES-ja.md) §1）。だから上の
EQB$`^\lambda`$ の例外の組も一致する。

- **定理 CORE-C$`^\Xi`$**（証明済み、FRAG なし）。$`\Xi_\omega`$ 以下のどの順序数も $`\mathrm{Core}(R_2^C)`$ に入る（届く先の上限と
  Carlson 2009, Thm 14.14 から）。前は $`\upsilon_{\omega^3}`$ までだった。査読者の注：上限から $`[0, \upsilon_{\Xi_\omega+\omega^2})`$ まで出る。
  いまは $`[0, \Lambda_\varepsilon)`$ と $`[0, \rho_{\Theta_P})`$ まで広がった（[REACHES-ja.md](REACHES-ja.md) §2）。
- **系**（証明済み）。FRAG なしで $`\min C^*_3 \ge \upsilon_{\Xi_\omega+\omega^2}`$、$`m_3 \gt \Xi_\omega`$。いまは $`m_3 \ge \Lambda_\varepsilon`$
  （[REACHES-ja.md](REACHES-ja.md) §5）。

確かめたこと：予言のある 25 個のやり直しの行列（$`V_3`$ から $`\Xi_\omega`$ まで）で、プログラムでの点の届く先は
$`\delta + c^*(\lambda)`$。証明書 79 個中 79 個を見つけて再生した（続く 19 個のやり直しと、60 組の $`M[N] \lt M`$）。逆向きは 19 個中 0 個。
査読者：$`\omega^{\omega^2}`$ 未満の 559 個のやり直しでずれの補題（違反 0）、新しい 11 個のやり直しの行列（すべて届く先
$`\delta + c(\lambda)`$）、証明書 10 個中 10 個を再生、Lean の名前の検査は緑。

## 4. 最初の不動点までの名前（定理 T+）

$`g(x) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot x)`$、$`s_1 = \sup_n g^n(0)`$ とおく。

- **定理 T+**（証明済み）。$`\eta \lt s_1`$ のすべてで $`\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$。また $`\Xi_1 = s_1`$。
  T-UP の前の上限 $`\Gamma_0`$ は仮定 (HA) からだけ来ていた。(HA) は $`\eta \lt g(\eta)`$ ならいつも成り立つ。
- $`s_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1})`$（証明済み、査読 2 回。[REACHES-ja.md](REACHES-ja.md) §2 の定理 T++）。
  これは README §6 の表の 26 行目の名前。
- だから **$`R_2^C`$ では $`[0, \Xi_1]`$ で Wilken の主張が成り立つ**（両方の半分）：そこのどの順序数も核に入り、つぶす引数が
  $`\Omega_\omega + \omega^{\theta+\Omega_1}`$ 未満の InaccPsi の標準形の値になる（補題 IS）。
- $`\Xi_1`$ のすぐ上の上からの名前（補題 REL）：$`\eta \lt \Gamma_0`$ で
  $`\upsilon_{\Xi_1+1+\eta} \le \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1} + \theta\cdot(1+\eta))`$（証明済み）。いまは
  $`\Xi_1 + 1 + \eta \lt \Xi_2`$ のすべての $`\eta`$ で等式で、主張は $`\Phi_1`$ まで成り立つ（[REACHES-ja.md](REACHES-ja.md) §2）。

## 5. 構造定理に向けて（Wilken 2021, Thm 4.2）

Wilken の Thm 4.2 は、$`+`$ の無い $`R_2`$ の $`\le_1`$ と $`\le_2`$ を、長さ 3 の最小の $`\le_2`$ の鎖より下で書き表す。その命題、証明の
地図、道具を書き出した（引用。査読者が論文と照らした）。主な 2 つの道具、平行移動と、追跡の鎖の添字の基の付け替えは、
$`+`$ があると振る舞いが変わる：

- $`+`$ で壊れる：平行移動の写像、値の「倍数」の形、彼の $`\mathrm{dp}`$ の中の $`R_1`$ の式。
- 変わる：基の付け替えは添字ではなく順序数に働く。
- 残る：彼の Lemma 1.7 と Prop 1.6。

$`+`$ の無い $`R_2`$ をそのまま写した「$`\varepsilon_0\cdot\iota \mapsto \upsilon_\iota`$」は偽：$`\lambda = \omega^\omega`$ で、$`+`$ の無い $`R_2`$ の
届く先は $`\delta + \omega + 1`$ だが、$`R_2^+`$ では高々 $`\delta + \omega`$（§3）。

証明済みの小さな補題：**L17-1**（Wilken 2021 の Lemma 1.7(1) の $`R_2^S`$ と $`R_2^C`$ 版）。**C-3.1**（彼の Lemma 3.1 の $`R_2^C`$ 版。
1 行の直しのあと）。**CORE-MIN**（$`\kappa_C`$ には $`\lt_1`$ の前の元も $`\lt_2`$ の後の元も無い）。**PRED2-FIN**（核の中では、
$`\lt_2`$ の前の元の集合はどれも有限。定理 CC を使う）。**TOP-GEN**（点の届く先を抑える 1 つの補題、両方の構造）。

**概略：** 定理 BLK$`^F`$-UP（$`\upsilon_{\Xi_1}`$ より下の組、ブロックの上限、やり直しの届く先の上限。$`R_2^S`$）。査読者は反証
しなかったが、すべての段を 1 行ずつは確かめていない。§3 の定理 BLK$`^\Xi`$ が両方の構造で証明済みなので、そちらで
足りる。査読は止める点を 1 つ見つけた。それは「このファイルが $`R_2^C`$ での TOP$`_3`$ という障害を取り除く」という主張への
もの（証明したのは $`R_2^S`$ 版だけ）。$`R_2^C`$ での TOP$`_3`$ は、代わりに §3 の補題 TOP$`_\lambda`$ で証明済み。

**予想 42+.I**（$`\upsilon_{\Xi_1}`$ より下。定理 T+ で InaccPsi の項で書く）：$`\lt_2`$ の組は、適当な $`A`$ について
$`\psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1}) \lt_2 \psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1} + \theta)`$ だけ。各ブロックの中では
$`R_2^+`$ は上端で切った $`R_1^+`$。やり直しの点 $`\upsilon_\lambda`$ の届く先はちょうど $`\delta_\lambda + (-1 + \mathrm{logend}\,\lambda)`$。組と
ブロックの部分は証明済み（§3）。届く先の正確な値も証明済みで、$`\upsilon_{\Xi_1}`$ より下ではこの予想は定理
（[REACHES-ja.md](REACHES-ja.md) §2）。**第 II 部**（$`\upsilon_{\Xi_1}`$ から
$`\psi_{\Omega_1}(I_\omega)`$ まで）：形しか分かっていない。手に入るどの論文も定義していない演算が要る。

## 6. 未解決

$`\Xi_\omega`$ より上の未解決の問題は [REACHES-ja.md](REACHES-ja.md) §7 にまとめた。前のリストのうち、補題 RS$`_\lambda`$、
$`\Xi_\omega`$ より先のずれ（$`\Lambda_\varepsilon`$ まで）、$`s_1`$ の等式は証明済みになった（[REACHES-ja.md](REACHES-ja.md) §1–2）。ここに残るもの：

- $`V_3`$ より上での変換の順序の命題 S（届く先は $`\Lambda_\varepsilon`$ まで分かった。新しい頭の部分での順序の証明が無い）。
- $`\upsilon_{\omega^3}`$ より上での $`R_2^S`$ の核（定理 CORE-S はそこで止まる）。
