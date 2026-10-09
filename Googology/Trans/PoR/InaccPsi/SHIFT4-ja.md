[← Back](README-ja.md) | [English](SHIFT4.md) | [Japanese](SHIFT4-ja.md)

# $`R_2^+`$ の 23 回目と 24 回目：FRAG のもとで $`\nu_C \ge X_{18}`$、閉じた届く先とちょうどの届く先、$`\Omega_k`$ での平ら、$`\Phi_3`$ の形、$`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ の先へ行く素の符号

このページは [SHIFT3-ja.md](SHIFT3-ja.md) の続き（そこの §2 が 22 回目）。§1 が 23 回目、§2 が 24 回目。25 回目と 26 回目は [SHIFT5-ja.md](SHIFT5-ja.md)、27〜29 回目は [SHIFT6-ja.md](SHIFT6-ja.md)、30 回目は [SHIFT7-ja.md](SHIFT7-ja.md) にある。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことの言い直しにすぎないと言った結果は、進みとして数えない。

## 1. 23 回目

4 つの論文（2026-10）。どれも 1 回ずつ査読された。だからこの節の結果は、回数を書いていなければ査読 1 回。**査読 2 回** とは、22 回目の査読者が
直しを出した（またはその結果を確かめた）うえで、この回の査読者が書き出したものをもう一度確かめたもの。どの論文も Wilken, JSL 72 (2007)、
Carlson, AML 38 (1999)、Wilken, AML 45 (2006)、Carlson 2009, p. 97 が予告する同値を使わない。ここで引く論文：Wilken, "Ordinal arithmetic based on Skolem hulling",
APAL 145 (2007)（以下 [W07a]。Def 3.1、Thm 3.23、Def 4.11、Def 7.5、Cor 7.6、L.8.1 の証明）、Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007)
（以下 [W07b]。L.2.1、Thm 2.2、Def 4.1、L.4.2、Cor 5.10）。Lean のファイルは足していない：2 つの論文（§1.2、§1.4）が項を比べるだけの Lean のファイルを確かめた
（`#eval`、定理は無い。緑で、査読者の再実行でも緑）。これらは確かめた扱い。22 回目の査読の細かい点は、[SHIFT3-ja.md](SHIFT3-ja.md) §2 とこの節で反映した。
段の番号は [SHIFT-ja.md](SHIFT-ja.md) と同じ（論文より 1 つ大きい）。

この回の新しい名前（$`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$ と $`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ は [SHIFT3-ja.md](SHIFT3-ja.md) §2 と同じ）：

```math
\zeta^* = \psi_{\Omega_3}(\Omega_\omega + \Omega_3),\qquad G(\Omega_3) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3),\qquad G(\Omega_3 + 1) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3 + \theta_2).
```

### 1.1 閉じた届く先、lh ずらしでのちょうどの蓋、$`\zeta^*`$ より下の層：FRAG のもとで $`\nu_C \ge X_{15}`$

記号は [SHIFT3-ja.md](SHIFT3-ja.md) §2.1 と同じ。やり直し $`\lambda`$ の区域のブロックは $`(\delta_j, \delta_{j+1}]`$。$`\upsilon`$ 点 $`b`$ について $`\mathrm{seg}(b) = [b, b^\infty)`$、$`b^\infty`$ は次の $`\upsilon`$ 点。
$`\mathrm{lh}_1`$ は $`R_1^+`$ での Wilken の届く先。$`\mathrm{seg}(\delta_j)`$ の点 $`y`$ が **閉じている** とは、$`(\delta_j, y]`$ のどの加法的主数 $`\alpha`$ でも $`\mathrm{lh}_1(\alpha) \le y`$ となること。$`\mathrm{LC}^S(y)`$ は
そこでの $`y`$ 以上の最小の閉じた点（無ければ $`\delta_{j+1}`$）。**lh ずらし** $`\mathrm{LHF}`$ は、$`\delta_j\cdot\omega`$ より下では恒等写像で、その上では $`y`$ のカントールの標準形の先頭の項 $`x`$ を
$`\mathrm{lh}_1(x)`$ に置きかえる。

- **22 回目の査読の細かい点を反映した**（証明済み、**査読 2 回**）。Wilken の側は系 $`T^{\Omega_m}`$（$`\tau = \Omega_m`$ とした [W07a] Def 3.1）の中で走らせる。そこでは Thm 3.23 により
  $`\Omega_{m+1}`$ より下のどの順序数も項。PSI-n の言い切っていた 2 つの段階に議論を付けた（高い基の型の候補、項の大きさについての帰納法）。読み方 $`\Theta_\nu`$ が上への写像なのは
  $`\pi_{\eta_\nu}`$ より下だけで、上からの評価は形の読み方を使う。$`\upsilon_{a+1} = \upsilon_a^\infty`$ の出どころは [W07b] Cor 5.10。
- **CLOSED-REACH**（証明済み、FRAG 無し）。どの届く先も $`R_2`$ で閉じている（SKEL⁺）。ブロック $`(\delta_j, \delta_{j+1}]`$（$`j \ge 1`$）の中の閉じた点は、$`\mathrm{seg}(\delta_j)`$ の閉じた点と
  $`\delta_{j+1}`$。だから $`[\delta_j^\infty, \delta_{j+1})`$ にある届く先は無い。
- **TOP-REG$`^\omega`$**（証明済み、FRAG 無し）。$`y \in [\delta_j, \delta_{j+1})`$、$`y \gt \delta_1`$ が映されていなければ、$`r(\lambda) \le y`$ か $`r(\lambda) = \mathrm{LC}^S(y)`$。**[SHIFT3-ja.md](SHIFT3-ja.md) §2.1 が足りない
  補題とした文字どおりの規則 $`r(\lambda) \le y`$ は偽**（FRAG のもと）：$`\tau_\nu = \omega^{G(\omega+1)+\omega}`$、$`y = \omega^{\delta_\nu+\omega}`$ で $`r(\nu) = y + 1`$（NO-NAIVE。そのようなやり直しは $`X_{14}`$ より下にある）。
  **REACH$`^{\mathrm{full}}`$**：どの短いやり直しでも $`r(\lambda) = \mathrm{LC}^S(y_0)`$。$`y_0`$ は $`\delta`$ より上で映されていない最小の点（「$`\le`$」は FRAG 無し、「$`=`$」は FRAG のもと）。
- **閉じた点**（ROOT、LOCAL、TRANS-E。証明済み）。$`\varphi(\omega, \delta_j + 1)`$ より下では、どの主数 $`\alpha`$ も $`\mathrm{lh}_1(\alpha) \lt \alpha\cdot\omega`$（例えば $`\omega^a`$ が $`\varepsilon`$ 数でなければ
  $`\mathrm{lh}_1(\omega^a) = \omega^a + \mathrm{logend}(a)`$）。そこでは lh ずらしが閉じた点を数え上げ、基の取り替えと入れ替えられる。
- **定理 EXACT-CL**（証明済み。「$`\le`$」は FRAG 無し、「$`=`$」は FRAG のもと）。$`\rho_{\nu+\omega^2} \le \nu_S`$ で $`\tau_\nu \lt \varphi(\omega, G(\omega+1)+1)`$ のどのやり直し $`\nu`$ でも
  $`r(\nu) = \mathrm{LHF}(\delta_\nu + o_\nu(\tau_\nu))`$。だから $`r(\nu) = \delta_\nu + o_\nu(\tau_\nu)`$ がちょうど成り立つのは $`\tau_\nu \lt \omega^{G(\omega+1)+\omega}`$ のとき（前は $`G(\omega+1)\cdot\omega`$ まで）。（査読者：
  範囲を決める等式 $`\Theta_\nu(\varphi(\omega, G(\omega+1)+1)) = \varphi(\omega, \delta_\nu+1)`$ は証明無しに書かれている。§2.1 の PHI-COMM で証明された。）**仮定つき。数えない**：ブロック $`j \ge 2`$ での同じ式。未解決の命題
  GAP$`_i`$（$`i \lt j`$）のもと。
- **長いやり直し**（証明済み、FRAG のもと）。$`D \lt G_2`$ の $`m_\lambda = G_2\cdot D + m_0`$ での R-CAP$`^O`$、LB、EXACT-LONG、CROSS-O、LONG-CLASS（前は $`D \lt \theta`$）、
  $`m_0 \lt \varphi(\omega, G(\omega+1)+1)`$ での lh ずらしつきの EXACT-LONG。使うピンの補題は MULTI-RC\*（[SHIFT2-ja.md](SHIFT2-ja.md) §1.1）の場合だと査読者が言うので、それ自体は数えない。
  [SHIFT3-ja.md](SHIFT3-ja.md) §2.1 が $`D \ge \theta`$ について挙げた障害は書き方の上だけのものだった。
- **$`\zeta^*`$ より下の乗数の層**（証明済み、FRAG のもと。置き換えの一覧として。査読者は、見つけたどの場所でも置き換えた入力を確かめ、場所を書き出すよう求める）。
  基 $`\ge \theta_2\cdot\omega^2`$ での $`G_2`$ より下の η ずれの D′-UNC（FRAG 無し）。1 段上の数える規則 PSI-θ（乗数 $`\psi_{\Omega_3}(\Omega_\omega + \delta)`$、高い基 $`\theta_2`$）。$`Z`$ より下の η ずれを越える
  移し、ピン、遠くの規則（その前置のやり直しは $`\tau \lt Z \lt G(1)`$ で、そこでは EXACT-O$`^\theta`$ が使える）。$`G_2 \le m \lt G(\Omega_3)`$ のどの符号でも **R-CAP**。$`\theta_2 \le M \lt \zeta^*`$ の
  $`\Omega_2`$ の定数無しの倍数 $`M`$ での CROSS-SHARP。**CEIL**（FRAG 無し）：$`m_u \ge G(\Omega_3)`$ なら $`\eta_u \ge \Omega_3`$。ここで $`\zeta \lt \zeta^*`$ なら $`G(\zeta) \lt G(\Omega_3)`$ で、
  $`G(\Omega_3)`$ はそれらの上限。
- **定理 X15**（証明済み、FRAG のもと。上の R-CAP に立つ）：

```math
\nu_C \ge X_{15} = \psi_{\Omega_1}(\Omega_\omega + \Omega_3 + \omega^{G(\Omega_3)+1} + \omega^{G_2+1}),\qquad G(\Omega_3) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3).
```

だから **FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, X_{15}]`$ で両方の半分とも成り立つ**。$`\nu_S \ge X_{15}`$、$`X_{14} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_3) \lt X_{15} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$。
また（P-LOW）(P) を満たすどのやり直し $`a`$ でも $`m_a \ge G(\Omega_3)`$、$`\eta_a \ge \Omega_3 + \omega^{G(\Omega_3)+1}`$。§1.4 はさらに先の $`X_{16}`$ まで行く。

- **未解決**（GAP$`_j`$、ROOT-CL、EXACT-CL\* は §2.1 で証明された）：GAP$`_j`$（$`\tau_\nu \in [\varphi(\omega, G(\omega j+1)+1), G(\omega j+2))`$ で $`r(\nu) \lt \delta_{j+1}`$）と ROOT-CL（主数 $`x`$ について、$`\alpha \le_1 x`$ となる最小の主数 $`\alpha \gt \delta_j`$ が $`x`$ の
  閉包に入る）。これらが $`[\theta, G_2)`$ 全体でのちょうどの届く先を与える（予想 EXACT-CL\*：$`r(\nu)`$ は $`\delta_\nu`$ より上の $`o_\nu(\tau_\nu)`$ 番目の閉じた点）。その隙間にある $`D`$ か $`m_0`$。
  §1.4 より先の符号。(P)、(Q′)、$`\nu_C`$ の InaccPsi による上からの評価。
- 査読者のほかの細かい点（§2.1 で反映）：「文字どおりの規則は偽」には「FRAG のもと」と書くこと。CEIL の 1 つの段階は確かめただけ（査読者が 2 行の証明を出した）。P-LOW の 1 行が
  抜けている。遠くの区域での閉じていることは自分の区域より多くを要する（使うのは安全な向きだけ）。名前が 2 つぶつかる。例の 1 つは 1 点低いところで確かめられていた。

### 1.2 $`\upsilon^*`$ の先へ行く素の符号

記号は [SHIFT3-ja.md](SHIFT3-ja.md) §2.2 と [SHIFT2-ja.md](SHIFT2-ja.md) §3.2 と同じ：$`\Xi_\omega = \sup_n \Xi_n`$。$`\Xi'_\omega`$ は $`P = \sup_n P_3^{(n)}`$ での $`\vartheta^2_P`$ の最小の不動点。$`Z''_\omega`$ は
$`\theta_{\Xi'_\omega}`$ の最小の不動点。$`\hat G = G(\Omega_2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$。

- **22 回目の査読の進行を止める点を直した**（証明済み、**査読 2 回**）。$`\Xi'_\omega`$ の系は $`\Xi_2`$ より下で純な系と一致し、パラメータを抑えることは純なパラメータでも成り立つ
  （CNST-PURE。新しい場合 1 つを書き出した）。写像 $`f(\eta) = 1 + \eta`$ は 2 つの部分を一度に覆うので、つなぐものは無い：この写像に沿った EMB が成り立つのは、
  (E1) $`D \subset \Xi'_\omega`$ と (E2′) 非可算などの $`\eta \in D`$ でもパラメータが $`H(\eta)`$ より下、のときに限る。
- **定理 EN=EX**（証明済み。査読者が場合ごとに導き直した。数値の試しはできない）。[SHIFT2-ja.md](SHIFT2-ja.md) §2.2 の $`n`$ 個組の系（数え上げの組）と [SHIFT3-ja.md](SHIFT3-ja.md) §2.1 の系
  （ちょうどの段の組）は、同じ階層と同じ終点 $`\Xi_n`$、$`P_3^{(n)}`$ を持つ。パラメータは段 $`\ge 2`$ の境で一致し、可算な $`\varepsilon`$ 数では片向きに成り立つ。補題 G1（$`\zeta \lt \hat G`$ なら
  $`\zeta \lt G(\zeta) \lt \hat G`$）とあわせて：$`\Xi_n = \psi_{\Omega_2}(\varepsilon_{\Omega_n+1})`$（[SHIFT3-ja.md](SHIFT3-ja.md) §2.1 で残っていた問い）、$`\Xi_\omega = \theta`$、$`\sup_n P_3^{(n)} = \theta_2`$、$`\zeta \lt \hat G`$ で
  $`\vartheta^2_{\theta_2}(\zeta) = G(\zeta)`$、$`\Xi'_\omega = \hat G`$。**[SHIFT2-ja.md](SHIFT2-ja.md) §3.2 の予想した名前 $`\Xi'_\omega = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ は偽**。$`Z \lt G(1) \lt \hat G`$ だから。
- **(E1)、(E2′)、$`D`$ 全体での EMB**（証明済み）。だから素の符号で

```math
\upsilon^* \le \theta_{\Xi'_\omega}(0) \lt Z''_\omega \le \iota(\mathrm{CH}_3),\qquad \iota(\mathrm{CH}_2) \ge Z_\omega \ge \Theta_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2}).
```

1 つ目は **$`\upsilon^*`$ の先へ行く最初の素の評価**（[SHIFT3-ja.md](SHIFT3-ja.md) §2.2 で求めたもの）。2 つ目は予想 $`Z_\omega = \Theta_1`$（[SHIFT2-ja.md](SHIFT2-ja.md) §2.2）の下半分。

- **PUSH**（移しとして証明済み：$`D'`$ での RED-DICT を使い、それは移しの形の GEN⁺ に立つ）。写像 $`g \mapsto \psi_{\Omega_2}(\Omega_\omega + \theta\cdot g)`$ で、素の符号で
  $`\iota(\mathrm{CH}_3) \gt \theta_{\Xi'_\omega}(0) \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2}) \gt \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\theta_2) \gt \upsilon^*`$。
- ここで名前の付いた評価（$`\upsilon^*`$、$`\Theta_1`$、$`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$）は、知られた素でない $`\iota(\mathrm{CH}_2) \gt \nu_C \ge X_{14}`$ より下にある（確かめた）。だから順序数の評価
  としては何も足さない。値打ちは、素の部品の系がそこに届くこと（RED-TOWER が要るもの）。
- **未解決**（PSI$`^W`$、段階の系での EN=EX、CNST$`^W`$ は §2.4 で証明された）：PSI$`^W`$（どの段でも基 $`\Omega_\omega`$ の上での数える規則。組 $`4 \times 11{,}990`$ 個で確かめた）、[SHIFT3-ja.md](SHIFT3-ja.md) §1.2 の段階の系での EN=EX、CNST$`^W`$。
  この 3 つのもとで、素の符号で $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$（仮定つき。数えない）。ほかの未解決：$`\Theta_1`$ より先の $`\mathrm{CH}_2`$、
  $`\theta_{\Xi'_\omega}(0) \gt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$ かどうか。
- 査読者の細かい点（§2.4 で反映）：形と CNST$`^\theta`$ を、書かれた範囲を越えて $`\hat G`$ まで使っている（正しいが、そう書くこと）。1 つの試しが止まらなかったのは時間の上限のせいではなく、
  プログラムが限りなく再帰したから。EN=EX の証明は 3 か所で短すぎる。PUSH は移しと書くこと。小さい点が 2 つ。

### 1.3 $`\Phi_3`$ の形：3,166 個のうち 3,163 個

記号は [SHIFT3-ja.md](SHIFT3-ja.md) §2.3 と同じ。

- **22 回目の査読の細かい点を反映した**（**査読 2 回**）：BASE-PHI-G の 1 行の直し。芯 $`(0,0,0)(1,1,1)(1,0,0)(2,1,1)`$ の入力の確かめを走らせたので、それについて T2-G が
  成り立つ（標本に入っていないので数えない）。試しの探す上限を書いた。プログラムの辞書 1 つを扱った。コメント。
- **横の子の階段**（15 個の行列。証明済み）。階段の印と 5 つの引っかけの補題を持つ CHN-OPQ の仕組み。前置を分からないままにした 1 つの一般の段階による族の補題 FAM-S。
  導きの補題 **REFL**：ブロック 1 つの BASE-PHI-G で、まず頂点の届く先の中で T の頂点と内側の根の鎖で覆い、次に R1 で下へ動かす。TRANSFER-R がそれを族に沿って運ぶ。
- **深い階段**（8 個。証明済み）。道の印。入れ子の族 FAM-DS（段ごとに頂点 4 つ）。**NEST-C**：入れ子の族は、$`x \le_1 y\cdot 2`$ のどの組 $`x \lt_2 y`$ の $`C(x)`$ にも入る。NEST と TRANSFER-N。
- **ROOT**（1 個。証明済み）。道に横の子がある同じもの。族は段ごとに頂点 9 つで、その 1 つは自分自身に代入されたもの。
- **集計**（確かめた。$`3{,}163 = 3{,}139 + 15 + 8 + 1`$）：

| 類 | 行列 | どの $`n`$ でも証明済み | 未解決 |
|---|---|---|---|
| I | 581 | 581 | 0 |
| SUM | 603 | 603 | 0 |
| ROOT | 635 | 635 | 0 |
| III | 1,347 | 1,344 | 3 |
| 全部 | 3,166 | 3,163 | 3 |

- **残り**（3 個、類 III、$`t = 1`$。未解決。§2.3 で証明された）。入力は、ラベルが変わらず $`(2,0)`$ の鎖で伸びる。$`\mathrm{conv}(A[n])`$ には入れ子の元がおよそ $`n/2`$ 個あり、どれも次の元の最後の子で、
  $`n`$ の偶奇で分かれる。要るもの：入れ子 1 つごとに鎖の頂点を 2 つ使う引っかけを持つ鎖の印、元のための再帰の記号、族の補題、頂点とそれ自身の和の鎖の導き（あらすじ）。
  REFL は 3 個のうち 2 個で $`n \le 4`$ では効き（確かめた）、$`n = 5, 6`$ では効かない。
- 査読者の細かい点（§2.3 で反映）：FAM-S が証明しているのは元 $`K-2`$ までで、元 $`K-1`$ は直接の計算 1 つ。REFL の書き方の点 1 つ。引用 1 つ。チェックサムのファイルについての注 1 つ。
  数 1 つに 1 文要る。移しには「型の届く先は族の元を指さない」が要る。どの型でも正しいが、書くこと。

### 1.4 $`\nu_C = \nu_S`$：CAP-0 の最初の試しの例、$`\Omega_3`$ での平ら、FRAG のもとで $`\nu_C \ge X_{16}`$

記号は [SHIFT3-ja.md](SHIFT3-ja.md) §2.2 と §2.4 と同じ（$`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$）。$`u = H(\Omega_3) = \psi_{\Omega_1}(\Omega_\omega + \Omega_3)`$ はそこで挙げた CAP-0 の最初の試しの例で、
符号は $`G(\Omega_3)`$。$`f(x) = \psi_{\Omega_2}(\Omega_\omega + x)`$。$`M_n`$ は $`\theta_2`$ から $`x \mapsto \psi_{\Omega_3}(\Omega_\omega + x)`$ を $`n`$ 回くり返したもの。

- **PLATEAU**（証明済み、FRAG 無し）。$`G`$ は $`[\zeta^*, \Omega_3]`$ で一定で、値は $`G(\Omega_3) = \sup_{\zeta \lt \zeta^*} G(\zeta)`$。$`D'`$ は $`[\zeta^*, \Omega_3)`$ に点を持たない。だから $`u`$ より下の
  どのやり直しも $`\eta \lt \zeta^*`$ で符号は $`G(\Omega_3)`$ より下。符号 $`\ge G(\Omega_3)`$ には $`\eta \ge \Omega_3`$ が、符号 $`\ge G(\Omega_3+1)`$ には $`\eta \ge \Omega_3 + \theta_2`$ が要る。同じ平らは
  どの $`\Omega_k`$（$`k \ge 3`$）にもある。$`\Omega_2`$ では点 $`H(\Omega_2) = \upsilon^*`$ の符号は短い符号 $`Z`$。
- **FIX-Z、D-UNC$`^Z`$**（証明済み、FRAG 無し）。$`Z = \sup_n f^n(\theta)`$、$`[Z, \Omega_2]`$ で $`f = Z`$。$`\zeta^* = \sup_n M_n`$、$`\mathrm{Sh}(M_n) = f^n(\theta)`$。D-UNC は、どの基でも $`Z`$ より下の
  どの η ずれでも成り立ち、$`\eta + Z \in D'`$ となるのは $`\eta \ge \Omega_2`$ のときに限る。
- **ずれ $`Z`$ での TOP-REG、DICHOTOMY、LB-U**（証明済み、FRAG のもと）。$`r(u) \le r(H(\Omega_3 + Z))`$（ここで $`H(\Omega_3 + Z) = \psi_{\Omega_1}(\Omega_\omega + \Omega_3 + Z)`$）か、符号が
  $`[G(\theta_2), G(\Omega_3))`$ の $`u`$ より下のやり直しが共終に多くずれ $`Z`$ を越えて届くか。また $`r(u) \ge r(H(\Omega_3 + \theta))`$。
- **θ⁺ の層**（移しとして証明済み、FRAG のもと。査読者は乗数かずれによるどの入力も確かめたが、置き換えの一覧は書き直していない。これは [SHIFT3-ja.md](SHIFT3-ja.md) §2.1 の層が
  受け入れられたのと同じ基準）。$`[\theta_2, \zeta^*)`$ の乗数は $`\mathrm{Sh}`$ で読み、値は $`[\theta, Z)`$。平らのてっぺん $`\Omega_3`$ は上限の $`Z`$ と読む。$`G_2 \le m \lt G(\Omega_3 + 1)`$ のどの
  符号でも **R-CAP**。どの $`M_n`$ でも CROSS-SHARP。**PLAT-SHARP**：$`r(\lambda) \ge H(\eta_\lambda + Z)`$ となるのは $`m_\lambda \ge G(\Omega_3)`$ のときに限る。これは $`G(\Omega_3)`$ より下の符号についての
  §1.1 の R-CAP を含む。そちらは §1.1 で独立に証明された。
- **定理 R-U**（証明済み、FRAG のもと、θ⁺ の層を使う）。$`r(u) = r(H(\Omega_3 + Z))`$、だから $`r(u) \lt H(\Omega_3 + Z + \omega^2)`$：**$`u`$ で CAP-0 が成り立ち**、$`u`$ は自分を越えない。
  CROSS-SHARP を範囲の先まで読んだ予想 $`r(u) \ge H(\Omega_3 + \Omega_2)`$（[SHIFT3-ja.md](SHIFT3-ja.md) §2.4）は偽：$`[\zeta^*, \Omega_3)`$ の乗数は正規でないので、越える議論は $`Z`$ で止まる。
  （査読者：これは前の GHAT と CROSS-F の組（[SHIFT2-ja.md](SHIFT2-ja.md) §2.1）のちょうどの類比。）また EXACT-G：符号 $`G(\Omega_3)`$ のどのやり直しも、ちょうどそのずれ $`Z`$ にある
  やり直しと同じところまで届く。
- **$`G(\Omega_3 + 1)`$ より下のどの符号でも CAP-0**（証明済み、θ⁺ の層を使う）。だから LOW$`_x`$ には、符号が $`[G(\Omega_3+1), P')`$ で $`\eta \ge \Omega_3 + \theta_2`$ の自分を越える長いやり直しが
  要り、そのどれにも、ずれ $`\omega^{Z+1}`$ を越える符号 $`\ge G(\Omega_3+1)`$ の共終な尾がある（LOW-RED⁺、SC-PROP）。
- **LOW は決まっていない。**（§2.2 が READ の順序数の側と、$`G(\hat\zeta_2)`$ より下での蓋を証明する。）予想 READ（$`\Omega_\omega`$ より下のどの正規な乗数でも、その符号の区間の蓋の読み方があり、平らのてっぺんごとに上限をとる）は、$`P'`$ より下のどの
  符号でも CAP-0 を与え、だから LOW は偽となり、扇の計画の予想する名前のとおりに $`P'`$ が自分を越える最初の符号になる。（査読者：READ に出した閉じた式は $`\Omega_3`$ より下では
  間違いで、$`\zeta \ge \Omega_3`$ に限ること。論文の「LOW が偽の証拠」は注意。）
- **定理 X16**（証明済み、FRAG のもと、θ⁺ の層を使う）：

```math
\nu_C \ge X_{16} = \psi_{\Omega_1}(\Omega_\omega + \Omega_3 + \theta_2 + \omega^{G(\Omega_3+1)+1}\cdot 2),\qquad G(\Omega_3+1) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3 + \theta_2).
```

だから **FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, X_{16}]`$ で両方の半分とも成り立つ**。$`\nu_S \ge X_{16}`$、$`u`$ の区域全体が核に入り、$`X_{15} \lt X_{16} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$。
また（P-LOW）(P) を満たすどのやり直し $`a`$ でも $`e_a \ge G(\Omega_3+1) + 1`$、$`\eta_a \ge \Omega_3 + \theta_2 + \omega^{G(\Omega_3+1)+1}`$。θ⁺ の層無しでは、論文は
$`\nu_C \ge X_{14}^+ = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2\cdot 2} + \omega^{G(\theta_2)+1}\cdot 2)`$ を証明する（FRAG のもと）。

- **仮定つき。数えない。** 段 2 のやり直し $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\Omega_3)+1})`$ での CAP-1 には $`\nu_S \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$（例えば LOW が偽）が要る。LOW が偽なら：
  $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\theta_2)+1})`$、θ⁺ の層で $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\Omega_3+1)+1})`$（[SHIFT3-ja.md](SHIFT3-ja.md) §2.4 の $`Y_1`$ を上げる）。
- **未解決**：LOW、つまり符号が $`[G(\Omega_3+1), P')`$ での CAP-0（READ には、$`\Omega_3`$ を単位とする乗数の形、平らのてっぺんごとの読み方、指数 $`\ge G_2`$ でのピンが要る）。
  $`(L(\omega), L(\omega+1))`$ での (P)（符号 $`P'`$ での下からの評価が要る）。(P1)、(D1b)、(E4)。$`\nu_C = \nu_S`$。
- 査読者の細かい点（§2.1 で反映）：読み方の上への写像の命題の書き方が違う（使うのは前の回のもの）。段 2 での道具の目録には θ の層と θ⁺ の層を足すこと。段 2 での類比は仮定つきと
  書くこと。包の補題の仮定はどの $`g`$ でも成り立ち、そう書くこと。指数 $`Z`$ でのピンには区域の移しが要る。LEVEL-SHIFT と UNIF を前の範囲の先で使うところは、基の付け替えを
  書き出すこと。見た目の点 1 つ。

### 1.5 23 回目のあとの状態

24〜30 回目でこの状態は変わった。§2.5、[SHIFT5-ja.md](SHIFT5-ja.md) §1.4、§2.4 と [SHIFT6-ja.md](SHIFT6-ja.md) §1.4、§2.4、§3.4、[SHIFT7-ja.md](SHIFT7-ja.md) §1.4 を見よ。

- $`R_2^C`$ での Wilken の主張：$`[0, X_4]`$ では FRAG 無しで、$`[0, X_{16}]`$ では FRAG のもとで（$`[0, X_9]`$ は査読 2 回。$`X_{15}`$ と $`X_{16}`$ は置き換えの一覧として証明された層に立つ）、
  両方の半分とも成り立つ。核の側は $`[0, \nu_C]`$ で成り立つ。$`\nu_C`$ の InaccPsi による上からの評価は無い：名前の付いた組での (P) は未解決のまま。
- 届く先：どの届く先も閉じていて、短いやり直しの届く先は、映されていない最小の点より上の最小の閉じた点。$`\tau \lt \varphi(\omega, G(\omega+1)+1)`$ では lh ずらしでちょうど分かり、
  $`D \lt G_2`$ の長いやり直しでも分かる。
- $`\theta_0`$ より下の下からの評価のための計画：SRO より下の段は、標本 3,166 個のうち 3,163 個ですべての $`n`$ で成り立つ。素の符号で $`\iota(\mathrm{CH}_2) \ge Z_\omega \ge \Theta_1`$、
  $`\iota(\mathrm{CH}_3) \ge Z''_\omega \gt \upsilon^*`$（移しで $`\gt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$ も）、$`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$、$`\iota(\mathrm{CH}_4) \ge Z^{(3)}`$。
- 上からの評価：$`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ の InaccPsi の項による評価はまだ無い。
- $`\nu_C = \nu_S`$：LOW は決まっていない。CAP-0 はその最初の試しの例と、$`G(\Omega_3+1)`$ より下のどの符号でも成り立つ。残り：(P1)、(D1b)、(E4)。

### 1.6 23 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。名前、標準形、$`D'`$ への所属、順 $`X_{14} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_3) \lt X_{15} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$。$`X_{14}`$ より下の $`\tau = \omega^{G(\omega+1)+\omega}`$ のやり直し。標本 $`3 \times 4{,}000`$ 個
  での閉じた点の計算（失敗 0）。1 段上の PSI-θ と InaccPsi の順を組 $`3 \times 25{,}440`$ 個で比べた（食い違い 0）。Lean の確かめは無い。査読者：定数つきでの層の覆いの補題
  （先頭の原子およそ 6,900 個）、$`[\zeta^*, \Omega_3)`$ の $`\eta`$ は $`D'`$ に無いこと、例のやり直しの区域が $`X_{14}`$ より下にあること：違反 0。
- §1.2。名前、標準形、順を Python と Lean で（緑）。$`D'`$ の標本、つぶす写像、パラメータ、単調性（失敗 0）。組 $`4 \times 11{,}990`$ 個での PSI$`^W`$（食い違い 0）。査読者：走らせ直すと
  同じ出力。$`\hat G`$ までの符号で組 $`2 \times 35{,}910`$ 個での規則 PSI-θ、1,120 回の試しでの CNST$`^\theta`$、平らの項 168 個、パラメータの組 1,096 個：失敗 0。
- §1.3。型は $`n = 6, \dots, 9, 12, 16`$ でプログラムと一致する。引っかけの値を 1,125 回比べた。独立の確かめのプログラムが 228 個の解を確かめる。組 474 個で間違った成功は 0。
  査読者：遠い段での型（$`n = 13`$ まで）。移した解は通る（24 個中 24 個）。補題の文だけから書いた確かめのプログラムが、24 個の行列すべてを 10 個の段で受け入れ、わざと壊した
  427 個の解をすべて退ける。標本に無い前置 2,230 個での族の補題。失敗するはずの組 322 個で成功 0。
- §1.4。名前、標準形、$`D`$ への所属、順の鎖を Python と Lean で（緑）。項 328 個での平ら、ずれ 1,422 個での D-UNC$`^Z`$、乗数 70 個での読み方（食い違い 0）。査読者：定数つきの
  8 回の実行（符号 441 個での覆いの補題、$`k = 2, 3, 4`$ での平ら、否定の場合 231 個を含む $`[Z, Z + \Omega_1)`$ での $`D`$ への所属）：違反 0。Lean の再実行は緑で同じ出力。

### 1.7 未解決

24〜30 回目でこの一覧は変わった。今の一覧は [SHIFT7-ja.md](SHIFT7-ja.md) §1.6 にある。

- 上からの評価：$`\nu_C`$ について名前の付いた 1 つの組での (P) と (Q′)。(P) には §1.1 と §1.4 より先の蓋と、符号 $`P'`$ での下からの評価が要り、(Q′) には $`L(\omega)`$ の等最小の
  パターンが要る。$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価。
- FRAG のもとで $`X_{16}`$ より上の主張：GAP$`_j`$ と ROOT-CL（$`[\theta, G_2)`$ でのちょうどの届く先）。$`D \ge G_2`$ の長いやり直し。$`\eta \ge \Omega_3`$ で符号 $`\ge G(\Omega_3+1)`$ の層
  （$`\Omega_3`$ を単位とする乗数の形、平らのてっぺんごとの読み方、指数 $`\ge G_2`$ でのピン）。
- 最初の到達不能基数：$`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_2})`$ の先へ行く素の符号（PSI$`^W`$、段階の系での EN=EX、CNST$`^W`$）。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。$`\omega^\omega`$ 以上の
  段階、非可算の段階の添字、$`\Omega_{\omega+1}`$。§1.3 の 3 個の行列での SRO より下の UNIF-FS。
- $`\nu_C = \nu_S`$：LOW（符号が $`[G(\Omega_3+1), P')`$ での CAP-0、予想 READ）、LOW$`^\omega`$、(P1)、$`P'`$ 以上のずれでの長いやり直しの TC⁺、(D1b)、(E4)。
- 名前：$`R(\Theta_{d\omega})`$；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ；$`D \ge G_2`$ の長いやり直しの正確な届く先；$`X_{16}`$ より先の名前；
  [COVER-ja.md](COVER-ja.md) §9 の残り。

## 2. 24 回目

4 つの論文（2026-10）。どれも 1 回ずつ査読された。だからこの節の結果は、回数を書いていなければ査読 1 回。**査読 2 回** とは、23 回目の査読者が
直しを出した（またはその結果を確かめた）うえで、この回の査読者が書き出したものをもう一度確かめたもの。どの論文も Wilken, JSL 72 (2007)、
Carlson, AML 38 (1999)、Wilken, AML 45 (2006)、Carlson 2009, p. 97 が予告する同値を使わない。ここで引く論文：§1 と同じ [W07a]（Def 3.28、L.3.30、Conv 4.1、Def 4.6、L.4.7）
と [W07b]（L.2.1、Thm 2.2、L.4.2、Thm 5.3 の証明、Cor 5.10）。Lean のファイルは足していない：3 つの論文（§2.1、§2.2、§2.4）が項を比べるだけの Lean のファイルを確かめた
（`#eval`、定理は無い。緑で、査読者の再実行でも緑）。これらは確かめた扱い。23 回目の査読の細かい点は、この回の論文がすべて反映し、この回の査読者がもう一度確かめた
（**査読 2 回**）。段の番号は [SHIFT-ja.md](SHIFT-ja.md) と同じ（論文より 1 つ大きい）。

この回の新しい名前（$`G`$、$`Z`$、$`\zeta^*`$、$`f(x) = \psi_{\Omega_2}(\Omega_\omega + x)`$ は §1 と同じ。$`\zeta^*_1 = \zeta^*`$、$`\bar Z_1 = Z`$）：

```math
\zeta^*_a = \psi_{\Omega_3}(\Omega_\omega + \Omega_3\cdot a),\qquad \bar Z_a = \psi_{\Omega_2}(\Omega_\omega + \Omega_2\cdot a)\ (1 \le a \le \omega),\qquad \theta_3 = \psi_{\Omega_4}(\Omega_\omega),\qquad \tau_{\mathrm{LH}} = \varphi(\omega, G(\omega+1)+1).
```

### 2.1 区間の閉じた点、$`G_2`$ より下のちょうどの届く先、$`\Omega_3\cdot\omega`$ までの層：FRAG のもとで $`\nu_C \ge X_{17}`$

記号は §1.1 と同じ。加法的主数 $`x \in \mathrm{seg}(b)`$ の **根** $`\alpha_x`$ は、$`\alpha \le_1 x`$ となる $`(b, x]`$ の最小の加法的主数 $`\alpha`$。$`\mathrm{lt}(c)`$ は $`c`$ のカントールの標準形の先頭の項。

- **§1.1 と §1.4 への 23 回目の査読の細かい点を反映した**（証明済み、**査読 2 回**）。その中の **PHI-COMM**（証明済み、査読 1 回）：置き換えも読み方 $`\Theta_\nu`$ も、ヴェブレンの
  標準形の項の上で $`\omega^x`$ と $`\varphi`$ と入れ替えられる。だから $`\Theta_\nu(\tau_{\mathrm{LH}}) = \varphi(\omega, \delta_\nu + 1)`$。これは EXACT-CL の範囲を決める等式（§1.1）。（査読者：証明の中の不動点でない点の
  数え上げは基から数えなければならない。入れ替えはそれでも成り立つ。）ほかに：$`D'`$ が $`[\zeta^*, \Omega_3)`$ に点を持たないことの 2 行の証明、P-LOW の欠けていた 1 行、区域の移しを使う
  $`G(1)`$ より下のすべての指数での 1 つのピンの補題、$`[\theta_2, \zeta^*)`$ の形の数える規則への帰着を書き出したもの。
- **ROOT-LOC**（証明済み、FRAG 無し）。根 $`\alpha_x`$ は $`x`$ の $`b`$ 局所化に入る（[W07a] Def 4.6、L.4.7、L.3.30。査読者：[W07b] の Thm 5.3 の証明の主張 (1) と同じ議論）。
  だからどの移し $`S`$ でも $`S(\alpha_x) = \alpha_{Sx}`$。これが §1.1 の ROOT-CL の、使う形。
- **ENUM、COUNT**（証明済み、FRAG 無し。査読者はすべての場合を手でやり直した）。写像 $`e_b(c) = \mathrm{lh}_1(\alpha_{\mathrm{lt}(c)}) + (-\alpha_{\mathrm{lt}(c)} + c)`$（$`b\cdot\omega`$ より下では $`e_b(c) = c`$）は、
  $`\mathrm{seg}(b)`$ からその閉じた点の上への順序同型。$`\mathrm{LC}^S(y) = \max(y, \mathrm{lh}_1(\alpha_{\mathrm{lt}(y)}))`$。$`e_b`$ は $`\varphi(\omega, b+1)`$ より下では lh ずらしで、どの移しとも入れ替えられる。
- **定理 EXACT-CL\***（証明済み。「$`\le`$」は FRAG 無し、「$`=`$」は FRAG のもと）。$`\rho_{\nu+\omega^2} \le \nu_S`$、$`\tau_\nu \lt G_2`$ のどのやり直し $`\nu`$ でも $`r(\nu) = e_{\delta_j}(c_\nu(\tau_\nu))`$。ここで
  $`\tau_\nu \in [G(\omega(j-1)+2), G(\omega j+2))`$、$`c_\nu(\tau_\nu) = \delta_j + (-\delta_{j-1}^\infty + \Theta_\nu(\tau_\nu))`$（$`\delta_0^\infty = 0`$）。だから §1.1 の予想 EXACT-CL\* が成り立ち、**どの $`j`$ でも GAP$`_j`$ が成り立つ**（FRAG 無し）。
  例えば $`\tau_\nu = \tau_{\mathrm{LH}}`$ で $`r(\nu) = \varphi(\omega, \delta_\nu+1)\cdot\omega`$。$`D, m_0 \lt G_2`$ の長いやり直しでも同じ（EXACT-LONG-CL\*）で、$`G_2`$ より下のすべての指数でピンがある（FRAG のもと）。
  （査読者：$`\tau_\nu`$ は $`0`$ になりうるので、帰納法は EXACT-O$`^\vartheta`$ から始めること。上への写像についての 1 文は「$`=`$」を使うので FRAG のもと。）（26 回目の査読者：尾がその区間に留まるという規則には、証明が選ぶとおり尾の始まりを
  $`H(z_0)`$ より上にとることが要る。今の書き方のままでは $`\nu = H(\omega^\omega + \omega^2)`$ が反例。[SHIFT5-ja.md](SHIFT5-ja.md) §2.2。）
- **§1.1 と §1.4 の層を書き出した**（移しで証明済み、FRAG のもと、**査読 2 回**）。§1.1 の $`\zeta^*`$ より下の層は、§1.4 の θ⁺ の層のてっぺんより下の部分。θ⁺ の層を今は 20 の段階で
  書き、どの段階にも、変えた入力、その入力の証明、それが入る場所を付けた。§1.1 の査読者が求めたとおり。だから $`X_{15}`$ と $`X_{16}`$ は査読 2 回。（査読者：下からの評価の側の
  段階はあらすじ。それは $`X_{15}`$、$`X_{16}`$、$`X_{17}`$ には使わない。）
- **乗数 $`\Omega_3\cdot a + \zeta_L`$（$`a \lt \omega`$）と $`\Omega_3\cdot\omega`$ の層**（FRAG を使わない補題は証明済み。残りは移しで証明済み、FRAG のもと）。PLATEAU-SEG：$`G`$ は
  $`[\Omega_3\cdot a + \zeta^*_{a+1}, \Omega_3\cdot(a+1)]`$ で一定で、そこに $`D'`$ の点は無い。FIX-SEG：$`f_a(x) = \psi_{\Omega_2}(\Omega_\omega + \Omega_2\cdot a + x)`$ として $`\bar Z_{a+1} = \sup_n f_a^n(0)`$。D-UNC$`^{\mathrm{SEG}}`$：基 $`\eta \ge \Omega_3`$ か
  $`\eta \gt \Omega_2\cdot\omega`$ で、$`\bar Z_\omega + \Omega_1`$ より下のずれに D-UNC。読み方 $`R(\Omega_3\cdot a + \zeta_L) = \bar Z_a + R^{(a)}(\zeta_L)`$、$`R(\Omega_3\cdot\omega) = \bar Z_\omega`$。これらを入力にして：**$`G(\Omega_3+1) \le m \lt G(\Omega_3\cdot\omega+1)`$ の
  どの符号でも R-CAP**、$`G(\Omega_3\cdot\omega+1)`$ より下のどの符号でも CAP-0、$`2 \le a \le \omega`$ で $`r(H(\Omega_3\cdot a)) \le r(H(\Omega_3\cdot a + \bar Z_a))`$。（査読者：D-UNC の 1 つの場合、基が
  $`[\Omega_2\cdot a, \Omega_2\cdot\omega]`$ にある場合を使っているのに書いていない。それは正しく、確かめた。読み方の後続の段階の 1 つは、使う PSI-n の条項を名指すこと。）
- **定理 X17**（証明済み、FRAG のもと）：

```math
\nu_C \ge X_{17} = \psi_{\Omega_1}(\Omega_\omega + \Omega_3\cdot\omega + \theta_2 + \omega^{G(\Omega_3\cdot\omega+1)+1}\cdot 2),\qquad G(\Omega_3\cdot\omega+1) = \psi_{\Omega_2}(\Omega_\omega + \Omega_3\cdot\omega + \theta_2).
```

だから FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, X_{17}]`$ で両方の半分とも成り立ち、$`X_{16} \lt X_{17} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$。§2.2 はさらに $`X_{18}`$ まで進む。

- **未解決**：この層の下からの評価の側（$`a \ge 2`$ で $`r(H(\Omega_3\cdot a)) \ge H(\Omega_3\cdot a + \bar Z_a)`$）。届く先を符号で書く InaccPsi の式。
- 査読者のほかの細かい点：[W07b] Thm 5.3 を引くこと。記号 $`\mathrm{lh}_1`$ の「+ つき」を外すこと。入力の一覧を「完全な証明」と呼ぶ見出しが 1 つある。

### 2.2 読み方 READ：どの $`\Omega_k`$ でも順序数の側は証明済み、符号 $`G(\hat\zeta_2)`$ より下の蓋、FRAG のもとで $`\nu_C \ge X_{18}`$

$`\mathrm{Sh}`$ は段のずらし（$`\Omega_k \mapsto \Omega_{k-1}`$、$`\psi_{\Omega_k} \mapsto \psi_{\Omega_{k-1}}`$）。乗数 $`\zeta`$ が正規とは、$`G(\zeta)`$ が標準形であること。$`\zeta_H`$ は $`\zeta`$ のカントールの標準形の $`\Omega_3`$ 以上の部分で、
$`\zeta_L \lt \Omega_3`$ は残り。$`\gamma = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot(\omega+1))`$ として：

```math
\hat\zeta_0 = \theta_3\cdot(\omega+1) + \gamma\cdot\omega,\qquad \hat\zeta_1 = \theta_3\cdot(\omega+1) + \varphi(\omega, \gamma+1),\qquad \hat\zeta_2 = \theta_3\cdot(\omega+1) + \varphi(\omega, \gamma+1)\cdot\omega.
```

読み方はそれぞれ $`G(\omega+1)\cdot\omega`$、$`\tau_{\mathrm{LH}}`$、$`\tau_{\mathrm{LH}}\cdot\omega`$ で、$`\Omega_3 + 1 \lt \theta_3 \lt \hat\zeta_0 \lt \hat\zeta_1 \lt \hat\zeta_2 \lt \Omega_4`$（確かめた）。

- **READ を書き直した**（命題。§1.4 への査読者の直しを反映、**査読 2 回**）。定数の無い正規の乗数で、$`\zeta \lt \Omega_3`$ なら $`R(\zeta) = \mathrm{Sh}(\zeta)`$、$`\zeta \ge \Omega_3`$ なら $`R(\zeta) = f(\mathrm{Sh}\,\zeta_H) + \mathrm{Sh}(\zeta_L)`$。
- **どの $`\Omega_k`$ でも、$`\Omega_\omega`$ でも、順序数の側**（証明済み、FRAG 無し。査読者はすべての証明を導き直し、論文が標本を取っていない $`G(\Omega_5)`$ より上のずれ 1,273 個で試した）。
  $`\zeta`$ が正規 ⟺ $`\mathrm{Sh}(\zeta) \in D'`$（ALIGN）。$`R`$ は狭義増加で、$`[\theta_2, \Omega_\omega)`$ の定数の無い正規の乗数を、$`[P, P')`$ の定数の無いずれの上へ写す。$`R(\Omega_3) = Z`$、
  $`R(\Omega_k) = G(\Omega_{k-1})`$（$`k \ge 4`$）で、どれもその下の読み方の上限。正規の $`\zeta \in [\Omega_k, \Omega_{k+1})`$ で $`R(\zeta) \lt G(\Omega_k) \le G(\zeta)`$。$`R(\Omega_\omega) = G(\Omega_\omega) = P'`$。だから読み方は
  $`\zeta \lt \Omega_\omega`$ ではどこでも符号より下にとどまり、$`P'`$ で符号に会う。また $`G`$ は $`[\psi_{\Omega_k}(\Omega_\omega + \Omega_k), \Omega_k]`$ で一定（$`k \ge 3`$）で、基 $`\ge \Omega_k`$ で $`G(\Omega_k)`$ より下のずれに D-UNC。
- **蓋**（移しで証明済み、FRAG のもと）。$`\zeta`$ の区間の蓋は、前の区間の蓋と、$`R(\zeta)`$ のカントールの標準形の指数でのピンから出る。ピンは $`\tau_{\mathrm{LH}}`$ 以下のすべての
  指数にある（$`\tau_{\mathrm{LH}}`$ そのものでの新しい分離の補題）。だから **$`G(\Omega_3+1) \le m \lt G(\hat\zeta_2)`$ のどの符号でも R-CAP、$`G(\hat\zeta_2)`$ より下のどの符号でも CAP-0**。
  $`\hat\zeta_0`$ からは PHI-COMM（§2.1）の等式を使う。論文はそれを §1.1 の査読の未解決の項目として引いている。
- **定理 X18**（証明済み、FRAG のもと。§2.1 の PHI-COMM を使う。どちらも査読 1 回）：

```math
\nu_C \ge X_{18} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_2 + \omega^{G(\hat\zeta_2)+1}\cdot 2),\qquad G(\hat\zeta_2) = \psi_{\Omega_2}(\Omega_\omega + \hat\zeta_2).
```

だから **FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, X_{18}]`$ で両方の半分とも成り立つ**。$`\nu_S \ge X_{18}`$、$`X_{17} \lt X_{18} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$（$`\hat\zeta_0 \gt \theta_3 \gt \Omega_3\cdot\omega\cdot 2`$ なので
$`X_{17} \lt X_{18}`$）。PHI-COMM 無しでは、論文は $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_0 + \omega^{G(\hat\zeta_0)+1}\cdot 2)`$ を証明する。これも $`X_{17}`$ より上。LOW には今は、符号が $`[G(\hat\zeta_2), P')`$ にあり $`\eta \ge \hat\zeta_2`$ の、
自分を越える長いやり直しが要る。**仮定つき。数えない**：LOW が偽なら $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\hat\zeta_2)+1})`$（$`Y_1`$ をさらに上げる）。

- **未証明**（査読者の進行を止める点。どれも $`X_{18}`$ への道筋には無い。25 回目は、制限した鋭い形を証明し、2 つ目の点を正確にし、3 つ目を直した。[SHIFT5-ja.md](SHIFT5-ja.md) §1.1）：
  - $`\Omega_3 \le M \le \hat\zeta_1`$ での鋭い形「$`r(\lambda) \ge H(\eta_\lambda + R(M))`$ ⟺ $`m_\lambda \ge G(M)`$」は $`M = \Omega_3 + 1`$ で**偽**（FRAG のもと）：$`u = H(\Omega_3)`$ の符号は $`G(\Omega_3) \lt G(\Omega_3+1)`$
    なのに、R-U（§1.4）により $`r(u) \gt H(\Omega_3 + Z + 1)`$。「⟸」は成り立ち、「⟹」は $`R(M)`$ が $`\Omega_1`$ の倍数のときに成り立つ。
  - 「$`P'`$ より下のすべての符号でのピンから、どの $`\Omega_k`$ でも READ が出る」。$`G_2`$ より上の指数では、要る形の分離は偽（符号 $`G_2`$ のやり直しは長く、自分の区域の先へ
    届く）。そのような指数は $`\theta_3\cdot\omega^2`$ から現れる。だから $`\theta_3\cdot\omega^2`$ より先の READ には、行き先が遠い区域にある新しい上からの評価の規則が要る。
  - $`H(\Omega_4)`$ での二者択一（そこで CAP-0、またはその下で共終に多くの越え）。下からの評価 $`r(H(\Omega_4)) \ge H(\Omega_4 + \tau_{\mathrm{LH}})`$ は成り立つ。
- **止まる所**：$`\hat\zeta_2`$ には指数 $`\tau_{\mathrm{LH}} + 1`$ でのピンが要り、符号 $`\tau_{\mathrm{LH}}`$ と $`\tau_{\mathrm{LH}} + 1`$ での知られた下からの評価は一致する。（査読者：足りないのは $`\tau_{\mathrm{LH}}`$ での届く先の
  上からの評価。§2.1 の EXACT-CL\* が今それを与える（$`r = \varphi(\omega, \delta+1)\cdot\omega`$）が、そこから $`\tau_{\mathrm{LH}} + 1`$ でのピンを導いた論文はまだ無い。）（25 回目の査読者：下からの評価が一致するというのは注意にすぎず、行き先が $`\mathrm{lh}_1(\varphi(\omega, \delta+1))`$ までのときだけ正しい。ピンはある。[SHIFT5-ja.md](SHIFT5-ja.md) §1.1。）
- 査読者の細かい点：X18 の証明の場合分けの 1 つは間違いで、結論は最小の倍数の議論で成り立つ。尾の基には $`\kappa \ge H(\Omega_3)`$ が要る。lh ずらしの点でのピンにはそこでの
  H-RC が要る。定数の要るすきまのてっぺんでの上限 2 つは類比で言い切っている。言い回し。標本。

### 2.3 $`\Phi_3`$ の形：3,166 個すべて

記号は §1.3 と同じ。

- **23 回目の査読の細かい点を反映した**（**査読 2 回**）。
- **最後の 3 個（類 III、$`t = 1`$。証明済み）。** 入力はラベル $`(2,0)`$ の $`n+1`$ 個の頂点の鎖で伸びる（INPUT-CC）。鎖の頂点 1 つがプログラムの層 $`\Phi(t)`$ 1 つになり、
  lh は 2 層ずつ下がるので、元は $`k \equiv n`$（mod 2）の $`\Phi^k(\mathrm{core})`$。これが §1.3 の偶数と奇数の $`n`$ の分かれ。道具：鎖の印と、深さの分からない入れ子の印を持つ機関
  （CC-OPQ。引っかけの補題 5 つは、どれもプログラムと手で照らした）。族の補題 FAM-T：$`k \ge 3`$ で $`\mathrm{lh}(\Phi^k) = \Phi^k + \Phi^{k-2}`$。形の定理 CC-SHAPE（$`n \ge 9`$ で、14〜16 個の頂点の決まった型と
  元のブロック）。導きの補題 **SSC-G**：$`w_k \le_1 w_k + w_{k-1}`$ を満たす元 $`w_k`$ を、$`\zeta(g) \le_1 \zeta(g)\cdot 2`$ での R1 を繰り返して $`\zeta(g)`$ より下に作る。要るのは $`g + g \le \mathrm{reach}_T(g)`$ の
  T の頂点 $`g`$ が 1 つだけ（REFL にはおよそ $`n/2`$ 個要った）。TRANSFER-SSC。
- **数え上げ**（確かめた。$`3{,}166 = 3{,}163 + 3`$）：

| 類 | 行列 | すべての $`n`$ で証明済み | 未解決 |
|---|---|---|---|
| I | 581 | 581 | 0 |
| SUM | 603 | 603 | 0 |
| ROOT | 635 | 635 | 0 |
| III | 1,347 | 1,347 | 0 |
| 全部 | 3,166 | 3,166 | 0 |

- **標本での UNIF-FS**（証明済み、受け入れられた数え上げのもと）：標本のどの行列 $`A`$ とどの $`n`$ でも $`\iota(\mathrm{conv}\,A[n]) \lt \iota(\mathrm{conv}\,A)`$。
- **未解決**：SRO より下のすべての標準形のトリオ行列での段。$`A`$ について一様な機関による分類、標本に無い伸び方の印（鎖の上の鎖、入れ子の入れ子、周期 $`\gt 2`$）、
  形から導きを作る規則（今はデータを探索で見つけている）が要り、下からの評価には MU$`_{\mathrm{SRO}}`$ も要る。InaccPsi の基本列を通る道は手に入らない。
- 査読者の細かい点：TRANSFER-SSC には、決まった頂点と最後の区間がどの $`n`$ でも変わらないことが要る（正しく、確かめた。書くこと）。2 つの注意が、不可能性の証明のように
  読める（失敗したのは探索だけ）。注釈の行番号が古い。チェックサムのファイルについての注意 1 つ。

### 2.4 $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ の先へ行く素の符号

記号は [SHIFT3-ja.md](SHIFT3-ja.md) §1.2（段階 $`T \lt \omega^\omega`$、$`\Xi[k]`$、$`Z[k]`$）と §1.2 と同じ。$`\Xi^T`$ は段階 $`T`$ の終わりの点、$`Z^{[1,M]}`$ は段階 $`1, \dots, M`$ での IDX$`^p`$ の評価。

- **23 回目の査読の細かい点を反映した**（**査読 2 回**）：数える規則 PSI-θ は $`\Omega_\omega + \Omega_2^{\theta_2+1}`$ より下のどの正規の引数にも及ぶので、$`\hat G`$ までの形と CNST$`^\vartheta`$ はその帰結
  （外挿ではない）。CNST の試しが今は走る。EN=EX の短すぎた 3 か所を書き出した。PUSH は GEN⁺ の代わりに GEN-EXT（[BREAK-ja.md](BREAK-ja.md) §2）を引く。
- **定理 PSI$`^T`$、CNST$`^T`$、EN=EX$`^T`$**（証明済み。PSI-n が受け入れられたのと同じ、置き換えの一覧の水準。EN=EX$`^T`$ は数値では確かめられない）。どの段階 $`T \lt \omega^\omega`$ でも、
  段階 $`T`$ の系は、PSI-n の系に新しいてっぺんの単位 $`\Omega_{n+1}`$ を付けたもの。それは $`T`$ より前の段階の添字と、定数の無い添字 $`\psi_{\Omega_{n+2}}(\Omega_\omega\cdot T)`$ を持つ。数える規則は
  $`\beta \lt \Omega_\omega\cdot T + \Omega_{n+1}^{\psi_{\Omega_{n+2}}(\Omega_\omega\cdot T)+1}`$ のどの $`\psi_{\Omega_j}(\beta)`$ も計算し、パラメータは項から読め、数え上げの組の系とちょうどの段の組の系は一致する。$`T = 1`$ の場合が、
  §1.2 で未解決だった PSI$`^W`$、CNST$`^W`$、段階の系での EN=EX。
- **名前**（証明済み）：$`\Xi^T = \psi_{\Omega_2}(\Omega_\omega\cdot(T+1))`$。$`\Xi[\omega] = \psi_{\Omega_2}(\Omega_\omega\cdot\omega^\omega)`$ は [SHIFT3-ja.md](SHIFT3-ja.md) §1.2 の予想した名前。そこでのもう 1 つの予想した名前
  $`\theta_{\Xi[\omega]}(0) = H(\Xi[\omega])`$ は**偽**。
- **素の評価**（証明済み。鎖の長さ 3。GEN-EXT に立つ）。写像 $`\eta \mapsto \psi_{\Omega_2}(\Omega_\omega + \theta\cdot\eta)`$ は、$`\eta \in C_\eta`$ を満たすどの $`\eta \lt \Omega_\omega\cdot\omega`$ でも許されるので、素の符号で

```math
\iota(\mathrm{CH}_3) \ge Z^{[1,M]} \gt \theta_{\Xi^M}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot(M+1))\ (1 \le M \lt \omega),\qquad \iota(\mathrm{CH}_3) \ge Z[0] \gt \theta_{\Xi[0]}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega).
```

$`M = 1`$ が §1.2 で求めた $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ の先への評価。**これは知られた素でない評価を初めて越える素の評価**（FRAG のもとで $`\iota(\mathrm{CH}_3) \gt \nu_C \ge X_{18}`$ で、
$`X_{18} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$）。

- **ラベル**（査読者の点）。GEN-EXT は、GEN の証明をもっと広い定義域で走らせて証明された。それは GEN⁺ に「移し」のラベルを付けたのと同じ種類の証明（[THETA-ja.md](THETA-ja.md) §1）。
  このページ群は GEN-EXT を証明済み（査読 1 回、[BREAK-ja.md](BREAK-ja.md) §2）、GEN⁺ をその場合（[README-ja.md](README-ja.md) §4）と数えるので、上の評価は証明済みと数え、§1.2 の PUSH も証明済み。
- **仮定つき。数えない**（今は証明済み、[SHIFT5-ja.md](SHIFT5-ja.md) §1.3）：$`\Omega_\omega\cdot\omega`$ より先での GEN があれば、素の符号で $`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$。
- **未解決**：$`\Omega_\omega\cdot\omega`$ より先での GEN（$`\Omega_\omega`$ が $`P\cdot\eta`$ に吸い込まれると、GEN-EXT の取り出しの段階が働かないように見えた。実は働き、GEN はどの η でも成り立つ。[SHIFT5-ja.md](SHIFT5-ja.md) §1.3）。$`\omega^\omega`$ 以上の素の段階と非可算の段階の添字。
  $`\Theta_1`$ より先の $`\mathrm{CH}_2`$。
- 査読者の細かい点：わきの主張 1 つ（パラメータの集合は空でなく $`\{1\}`$）は偽だが害は無い。極限の段階では証明の 1 つの場合が空になり、直接閉じる。論文自身の試しは
  極限の段階に届いていなかった（査読者の試しは届く）。理由の書き方がゆるい所が 2 つ。（25 回目の査読者：PUSH の証明は $`P\cdot\Omega_k = \Omega_k`$ を使うが、$`k = 1`$ では偽。害は無く、$`k \ge 2`$ で足りる。）

### 2.5 24 回目のあとの状態

25〜30 回目でこの状態は変わった。[SHIFT5-ja.md](SHIFT5-ja.md) §1.4、§2.4 と [SHIFT6-ja.md](SHIFT6-ja.md) §1.4、§2.4、§3.4、[SHIFT7-ja.md](SHIFT7-ja.md) §1.4 を見よ。

- $`R_2^C`$ での Wilken の主張：$`[0, X_4]`$ では FRAG 無しで、$`[0, X_{18}]`$ では FRAG のもとで（$`[0, X_{16}]`$ は査読 2 回）両方の半分とも成り立つ。核の側は $`[0, \nu_C]`$ で成り立つ。
  $`\nu_C`$ の InaccPsi による上からの評価は無い：名前の付いた組での (P) は未解決のまま。
- 届く先：$`\tau \lt G_2`$ のどの短いやり直しと、$`D, m_0 \lt G_2`$ のどの長いやり直しでも、ブロックの $`c`$ 番目の閉じた点としてちょうど分かる（FRAG のもと）。どの $`j`$ でも GAP$`_j`$。
- $`\theta_0`$ より下の下からの評価のための計画：SRO より下の段は、標本の 3,166 個すべてですべての $`n`$ で成り立つ。素の符号で $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$
  （知られたどの素でない評価より上）、$`\iota(\mathrm{CH}_2) \ge \Theta_1`$。
- 上からの評価：$`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ の InaccPsi の項による評価はまだ無い。
- $`\nu_C = \nu_S`$：LOW は決まっていない。CAP-0 は $`G(\hat\zeta_2)`$ より下のどの符号でも成り立つ（FRAG のもと）。残り：(P1)、(D1b)、(E4)。

### 2.6 24 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §2.1。名前、標準形、$`D'`$ への所属、順 $`X_{15} \lt X_{16} \lt X_{17} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ を Python と Lean で（緑）。平ら、読み方、覆いの補題、ずれ 792 個での
  D-UNC$`^{\mathrm{SEG}}`$。抽象的な模型での ENUM（根を使わない変種は 2,153 回失敗する）：違反 0。査読者：$`\Omega_3`$ より下の 7 つの基でずれ 645 個での D-UNC、項 579 個での FIX-SEG、
  独立の模型の標本 12,000 個での ENUM：違反 0。Lean の再実行は緑で同じ出力。
- §2.2。正規の乗数 1,054 個での ALIGN、余白、順。ずれ 691 個での ONTO。703 個の場合（否定 268 個）での D-UNC。符号 187 個での覆い：失敗 0。Lean は緑。
  査読者：任意の引数を作る自前の生成器（組 490,000 個でのずらし、ずれ 1,515 個での ONTO、符号 2,680 個での定数つきの覆い、$`\hat\zeta_2`$ より下の指数）：失敗 0。
  自前の Lean のファイルと論文のものの再実行は、どちらも緑。
- §2.3。型は $`n = 24, 25`$ までプログラムと一致する。引っかけの値 324 個。独立の確かめのプログラムが 48 個の解すべてを受け入れる。わざと変えた解 1,008 個は退けられる。
  間違った組 598 個で成功 0。査読者：$`n = 17, \dots, 71`$ での型（165 個中 165 個）、命題の文だけから書いた 3 つ目の確かめのプログラム（126 個の段）、変種 1,808 個を退ける、間違った組 62 個、
  ランダムな 3,000 個の場合での FAM-T：失敗 0。Lean のファイルは無い。
- §2.4。段階 1、2 での規則と InaccPsi の順（組 $`12 \times 11{,}990 + 4 \times 183{,}612`$ 個）、10,560 回の試しでの CNST$`^T`$：食い違い 0。Lean は緑。査読者：極限の段階
  $`\omega`$、$`\omega+1`$、$`\omega\cdot 2`$、$`\omega^2`$（組 $`4 \times 11{,}990`$ 個、CNST の試し $`4 \times 1{,}120`$ 回）と、標本 120 個での素の評価の入力（4,920 回の試し）：失敗 0。Lean の再実行は緑。

### 2.7 未解決

25〜30 回目でこの一覧は変わった。今の一覧は [SHIFT7-ja.md](SHIFT7-ja.md) §1.6 にある。

- 上からの評価：$`\nu_C`$ について名前の付いた 1 つの組での (P) と (Q′)。(P) には $`G(\hat\zeta_2)`$ より先の蓋と、符号 $`P'`$ での下からの評価が要り、(Q′) には $`L(\omega)`$ の等最小の
  パターンが要る。$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価。
- FRAG のもとで $`X_{18}`$ より上の主張：指数 $`\tau_{\mathrm{LH}} + 1`$ でのピン。$`\theta_3\cdot\omega^2`$ より先では、行き先が遠い上からの評価の規則。$`\Omega_3`$ より上の層の下からの評価の側。
  $`\hat\zeta_2`$ より先の READ（$`\Omega_4`$ での平ら）。$`D \ge G_2`$ の長いやり直し。
- 最初の到達不能基数：$`\Omega_\omega\cdot\omega`$ より先での GEN。$`\omega^\omega`$ 以上の素の段階、非可算の段階の添字、$`\Omega_{\omega+1}`$。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準形の行列での段。
- $`\nu_C = \nu_S`$：LOW（符号が $`[G(\hat\zeta_2), P')`$ での CAP-0）、LOW$`^\omega`$、(P1)、$`P'`$ 以上のずれでの長いやり直しの TC⁺、(D1b)、(E4)。
- 名前：$`R(\Theta_{d\omega})`$；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ；届く先を符号で書く InaccPsi の式；$`X_{18}`$ より先の名前；
  [COVER-ja.md](COVER-ja.md) §9 の残り。
