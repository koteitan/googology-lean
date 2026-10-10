[← Back](README-ja.md) | [English](SHIFT9.md) | [Japanese](SHIFT9-ja.md)

# $`R_2^+`$ の 35 回目：$`L(G_2)`$ までの骨組みの届く先、$`\mathrm{Core}(R_2^S)`$ の最初の穴、$`\theta_0`$ へ向かう段階の道

このページは [SHIFT8-ja.md](SHIFT8-ja.md) の続き（そこの §2 が 34 回目）。§1 が 35 回目。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことの言い直しにすぎないと言った結果は、進みとして数えない。

## 1. 35 回目

3 つの論文（2026-10）。どれも 1 回ずつ査読された：$`G_2`$ より下のどの符号でも骨組みのやり直しの届く先を求める論文（§1.1）、(E) と $`\beta_0`$ の論文（§1.2）、素の符号の論文（§1.3）。
この節の結果は、回数を書いていなければ査読 1 回。$`[0, L(\varepsilon_{\Phi_\Omega+1}+\omega^2)]`$ での主張は初めの 2 つの論文がそれぞれ独立に証明したので、$`L(\varepsilon_{\Phi_\Omega+1})`$ から
$`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$ までの段階は **査読 2 回**。[SHIFT8-ja.md](SHIFT8-ja.md) §2.1 の査読の細かい点は 1 つ目の論文が反映し、その査読者がそれぞれの直しを確かめた（**査読 2 回**）。
2 つ目の論文は [SHIFT8-ja.md](SHIFT8-ja.md) §2.2 の結果を、その査読で直した形で使う。3 つ目の論文はそこの §2.3 の査読の細かい点を反映した（その査読者はこれについて別に判定を
出していない）。どの論文も Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない（査読者が確かめた）。引く論文：§1.1 は [SHIFT8-ja.md](SHIFT8-ja.md) と同じく
査読済みの段階を通してだけ。§1.2 は Carlson の [C11]、https://arxiv.org/abs/1104.1686（範疇性の定理 (a)–(d)、Claim 1、Cor 0.8、Cor 0.9。査読されていない preprint で、Claim 1 と重なりの段階は
34 回目に確かめ直した）と Carlson 2009（Def 5.2、Def 5.3、Def 5.4、L.5.5、L.5.7、Thm 14.10）。§1.3 の証明済みの段階はどの論文も使わず、FRAG も使わない。Lean のファイルは足していない：
§1.1 と §1.2 の順序数の入力は項を比べるだけの Lean のファイルで確かめた（`#eval`、定理は無い。緑で Python と同じ出力。査読者の再実行でも同じ）。§1.3 の 2 つの補題の抽象的な芯は
Lean のファイルで確かめた（緑、標準の公理だけ、`sorry` 無し。査読者が確かめ直した）。これらは確かめた扱い。段の番号は [SHIFT8-ja.md](SHIFT8-ja.md) と同じ（論文より 1 つ大きい）。
「FRAG のもと」もそこと同じ。

記号（[SHIFT8-ja.md](SHIFT8-ja.md) と同じ）：$`L(e) = H(\eta_e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$、$`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$、$`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$。骨組みのやり直し $`L(\lambda'')`$ は
符号 $`c''(\lambda'')`$ と組 $`(\tau''_j, \delta''_j)`$ を持つ。$`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$ は [SHIFT2-ja.md](SHIFT2-ja.md) §2.1 と同じで、$`G_2 = G(\omega^2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})`$、
$`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$。やり直し $`b = L(\lambda'')`$ について、**その区間の最初の区域** は $`[b, H(\eta_{\lambda''}+\omega^2))`$ で、$`\upsilon`$ の点 $`H(\eta_{\lambda''}+1+\zeta)`$（$`\zeta \lt \omega^2`$）を持つ。符号 $`c`$ について

```math
o_b(c) = \text{the order type of the codes } c' \lt c \text{ whose countable constants are all below } b.
```

（$`c`$ より下の符号 $`c'`$ のうち、可算の定数がどれも $`b`$ より下のものの順序型。）

### 1.1 FRAG のもとで、$`G_2`$ より下のどの符号でも骨組みの届く先、そして $`L(G_2)`$ までの主張

- **[SHIFT8-ja.md](SHIFT8-ja.md) §2.1 への査読の直し**（m1–m7。**査読 2 回**）。上に限りなく続く塔は $`t_0 = \Phi_\Omega+1`$ から始める (m1)。EXACT-G″ と TOP-REG″ は $`\lambda'' \lt \varepsilon_{\Phi_\Omega+1}`$ に
  限り (m2)、今は下のもっと広い定義域で証明し直した。$`\lambda'' = \Omega_1\cdot\omega`$ での使い方は移しと札を付けた (m3)。言い回し、札、標準形の決まり（m4–m6）。その査読の m7 はそれ自身が
  誤り：無限の $`x`$ では $`-1 + x = x`$ なので、前の札「$`\Phi_\Omega+1`$ までの符号」はちょうど正しかった（この回の査読者も同じ意見）。直しの確かめの 1 つの札が違う（下の m2）。
- **$`P'`$ より下の $`L`$ の定義域**（ARG-BOUND、DOM″、DOWN″、COF″、TAIL″。証明済み）。どの標準形 $`e \lt P'`$ でも、$`e`$ が $`L`$ の定義域に属すのは、$`e`$ のどの可算の定数も $`L(e)`$ より
  下であるときちょうど（前は $`e \lt \varepsilon_{\Phi_\Omega+1}`$ で）。ARG-BOUND：可算の部分項の外では、$`e`$ の中の値が非可算のつぶしの引数はどれも $`\Omega_\omega\cdot 2`$ より下。
- **どの $`\upsilon`$ の点でも読みの段**（READ$`^b`$。移しで証明済み、FRAG 無し）。1 つの $`\upsilon`$ の点での $`\theta`$ より下の符号の読み（[VEBLEN-ja.md](VEBLEN-ja.md) §1、§8、[SHIFT2-ja.md](SHIFT2-ja.md) §3.1、
  [SHIFT3-ja.md](SHIFT3-ja.md) §1.1、§2.1）は、基が $`\upsilon`$ の点であることしか使わないので、どの $`L(\lambda'')`$ でも成り立つ。引いた入力の 1 つは最初の段でしか述べられていないが、使われない (m6)。
- **定理 EXACT-O″：$`\Phi_\Omega`$ より上の Veblen の閉包と、$`\theta`$ より下のどの符号**（RED-O″、EXACT-O″。移しで証明済み、FRAG のもと）。符号 $`c = c''(\lambda'') \lt \theta`$ を持つ骨組みの
  どのやり直し $`b = L(\lambda'')`$ でも：

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + o_b(c).
```

  これは [SHIFT8-ja.md](SHIFT8-ja.md) §2.1 の予想 EXACT-O″ の $`\theta`$ より下の部分で、[SHIFT3-ja.md](SHIFT3-ja.md) §2.1 の読み EXACT-O$`^n`$ を 1 つ上に上げたもの。例：符号 $`\Gamma_{\Phi_\Omega+1} = \psi_{\Omega_2}(\Omega_2+1)`$ は
  $`\delta''_1 + \Gamma_{\Phi^b+1}`$ を与える。$`\Phi^b`$ は $`b`$ より上の $`\alpha \mapsto \Gamma_\alpha`$ の最小の不動点。査読者：上からの半分で、$`b`$ の切片を出る読みには次の項目の上からの規則の広げた形が
  要り、実際に使われているのはそれ (m5)。
- **$`\theta`$ から $`G_2`$ までの符号**（θ の読み、INDEX″$`_1`$、H-RC″$`_1`$、TOP-REG″$`^\theta`$、定理 EXACT-O″$`^\theta`$、ATTAIN″$`^\theta`$。移しで証明済み、FRAG のもと。査読者はどの場合も前の回の
  区域の留めと照らした）。$`[\theta, G_2)`$ の符号では、$`o_b`$ は [SHIFT3-ja.md](SHIFT3-ja.md) §2.1 の読みで、$`\nu`$ より上の $`\upsilon`$ の点の代わりに $`b`$ の区間の最初の区域の $`\upsilon`$ の点を使ったもの。
  たとえば $`o_b(\theta) = H(\eta_{\lambda''}+1)`$（$`b`$ の次の $`\upsilon`$ の点）で、$`o_b(G(\omega))`$ と $`o_b(G(\omega+1))`$ はその区域の最初の組の両端。だから行き先は $`[\delta''_1, \delta''_1\cdot 2)`$ にとどまり、最初の段での窓の
  障害（[SHIFT4-ja.md](SHIFT4-ja.md) §1.1）は起きない。骨組みの基の最初の区域での新しい留めが上からの規則 TOP-REG″$`^\theta`$ を与え、FRAG″ が下からの半分を与える：上の式は **$`G_2`$ より下のどの
  符号でも** 成り立つ。与えた符号に届くずれを持つ最小のやり直しも分かる（ATTAIN″$`^\theta`$）。
- **定理 C$`^\theta`$ と新しい最前線**（移しで証明済み、FRAG のもと）。$`L(G_2)`$ より下で、$`R_2^S`$ は点 $`L(e)`$ の骨組みについて骨組み型：どの新しい組も組 $`(\tau''_j, \delta''_j)`$ で、新しい組を
  含まない。どのやり直しもちょうどの届く先を持つ。扇の頂点も 3 重の入れ子も無い。だから $`\beta_0 \gt L(G_2)`$、$`R_2^C`$ の 3 重の入れ子の最小の上端はその上にあり、**$`R_2^C`$ での Wilken の
  主張は $`[0, L(G_2)]`$ で成り立つ**。両方の半分とも（名前の側はその点が標準形だから、補題 L）：

```math
L(G_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+G_2}),\qquad G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2}).
```

  途中の点（どれも両方の半分とも）：$`L(\psi_{\Omega_2}(\Omega_2+1))`$、$`L(\psi_{\Omega_2}(\Omega_2\cdot 2))`$、$`L(\psi_{\Omega_2}(\Omega_2^{\Omega_2}))`$（Veblen の閉包の終わり）、$`L(\psi_{\Omega_2}(\varepsilon_{\Omega_2+1}))`$、$`L(\theta)`$。覆われない最初の
  符号は、その点そのものでの $`G_2`$ で、その読みは区間の中の最初のやり直しになるはず。
- 査読者の細かい点（どれも結果を変えない）。1 つの例で、$`\lambda'' = G(\omega+1)\cdot\omega = \omega^{G(\omega+1)+1}`$ の符号は $`G(\omega+1)+1`$ で、$`G(\omega+1)\cdot\omega`$ ではない。だから 1 つの目印と確かめの 2 つの
  行の札が違う (m1)。m1 の直しの確かめの 1 つの札が違う点を名指す。主張は成り立つ (m2)。区間の中の骨組みの記述で「$`n \ge 1`$ または $`j = 0`$」は「$`n \ge 1`$」と読む。PIN-R は左端の届く先の
  評価を使うが、それはそこに書いておくべき (m3)。著者自身の手順の誤り（ディレクトリを移る命令が紛れ込んだが、失敗して何も変わっていない。m7）。
- **未証明**。PIN-R（区間の中の最初のやり直しでの留め）：m3 を除いて証明済みで、最前線には使わない。同じ議論が区間のどのやり直しでも効くこと：概略 (m4)。区間全体を通しての
  相対的な遠い留め：概略。$`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ より下のどの短いやり直しでもの EXACT-O″（読みが $`\delta''_1\cdot\omega`$ より下にとどまるもの）：予想。それにはその留めと、行き先が $`\delta''_1\cdot 2`$ 以上の
  ときの 1 つ上の窓の規則が要る。骨組みの長いやり直し（予想：ちょうど符号 $`\psi_{\Omega_2}(\Omega_\omega\cdot 2 + \psi_{\Omega_3}(\Omega_\omega\cdot 2)\cdot\omega^2)`$ から）、その着地の計算、$`P_3`$ より下の符号、$`\nu_3`$：
  未解決。残りの段階の順序は論文に書いてある。$`T_3 \le \nu_3`$ は主張していない。

### 1.2 (E)、$`\mathrm{Core}(R_2^S)`$ の最初の穴、$`\beta_0`$

言葉は [SHIFT8-ja.md](SHIFT8-ja.md) §2.2 のもの。$`f`$ は核の同型、$`\rho(\mu)`$ は $`\mu`$ の最小の $`\le_1`$ の前の点、$`x_F^C`$ は $`R_2^C`$ の最小の扇の頂点。$`\varepsilon = \varepsilon_{\Phi_\Omega+1}`$ と書く。

- **$`L(\varepsilon)`$ の区域**（PI-EPS、BLOCK″$`_0`$、EXACT-G″$`_\varepsilon`$、C$`^\#`$、AGREE$`^\#`$。移しで証明済み、FRAG のもと）。$`L(\varepsilon)`$ の符号 $`\varepsilon`$ は極限の符号で、$`b`$ でのその読みは
  1 つの項 $`\varepsilon_{\Phi^b+1}`$。基の取り替えはそれと交換する（Veblen の読みの $`\varphi`$ の場合）。だから

```math
r(L(\varepsilon)) = L(\varepsilon+\omega+1) + \varepsilon_{\Phi^{L(\varepsilon)}+1}
```

  で、$`L(\varepsilon)`$ の区域全体が骨組み型。$`\beta_0 \gt L(\varepsilon+\omega^2)`$、$`R_2^C`$ の 3 重の入れ子の最小の上端はその上にあり、主張は $`R_2^C`$ で $`[0, L(\varepsilon+\omega^2)]`$ で成り立つ。ここで
  $`L(\varepsilon+\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\varepsilon} + \omega^{P'+2})`$（§1.1 のこの部分の 2 つ目の証明）。1 つの評価には、名前の挙がっていない引用の事実が要る (m6)。
- **NO-GAP$`^\#`$**（証明済み、FRAG のもと）。$`[0, L(\varepsilon+\omega^2)) \subseteq \mathrm{Core}(R_2^S)`$ で、そこで $`f`$ は恒等。だから **$`R_2^S`$ での主張は $`[0, L(\varepsilon_{\Phi_\Omega+1}+\omega^2))`$ で成り立つ**。
  査読者：$`[0, L(\varepsilon))`$ はすでに [SHIFT8-ja.md](SHIFT8-ja.md) §2.1、§2.2 から出ていたので、増えたのは 1 つの区域で、論文が書くような $`L(\Omega_1\cdot\omega)`$ からの段階ではない (m7)。補題
  ROOT-CORE（証明済み、FRAG 無し：$`\rho(\beta_0)`$ は $`\le_1`$ の前の点を持たない $`p \le \beta_0`$ の最大のもの）はこれには要らない (m8)。
- **最初の穴**（GAP-AP、TWIN、MOVE-OBST、S-COVERED。証明済み、FRAG 無し）。$`\sigma_S`$ は加法的に主要で、$`[\rho(\beta_0), \beta_0]`$ にある。その双子 $`\gamma = f^{-1}(\sigma_S)`$ は、$`\sigma_S`$ より下に、
  $`\sigma_S`$ が $`R_2^C`$ で持つのと同じ $`\le_1`$ と $`\le_2`$ の前の点を持つ。$`\gamma`$ を含む $`R_2^S`$ のどの等極小の集合でも、$`\gamma`$ はそこで $`\lt_2`$ の左端か、その集合の $`\gamma`$ より下の点より上で、
  あとの点の最小の $`\le_1`$ の前の点。関係がどれも $`R_2^S`$ で成り立つ $`C`$ の等極小の集合は $`\mathrm{Core}(R_2^S)`$ に入り、そこで $`f`$ は恒等。査読者：1 つの句「$`\sigma_S \le \alpha`$ と $`f^{-1}(\alpha) \gt \alpha`$ は
  同値」は右から左しか証明されておらず、逆向きは出ない。この句は使われない (m1)。$`\gamma`$ が加法的に主要であることは書いておくべき (m5)。
- **β0-CHAR**（証明済み。**数えない**：査読者によれば、有限集合の試験 CMP の系（[ROUND1-ja.md](ROUND1-ja.md) §1）と Carlson 2009, Def 5.4 をあわせた言い直しで、新しいのは「Carlson で閉じた」という
  名前だけ、m4）。$`\beta_0`$ は、ある $`\alpha \lt b`$ が $`\alpha \le_k b`$ についての Carlson の条件（Def 5.3 を $`R_2^S`$ で読んだもの）を満たすのに、$`R_2^S`$ で $`\alpha \le_k b`$ でない、最小の $`b`$。
- **CL2-ONLY と SHARP-RIG**（証明済み）。$`R_2^S`$ の穴の中の $`\alpha`$ の蓋では、Carlson の $`\le_2`$ は Def 5.3 の 2 つ目の条件に帰着する。だから $`x_F^C`$ より下では、[SHIFT8-ja.md](SHIFT8-ja.md) §2.2 の条件 RIG は、
  型 N の最初の食い違いを除くのに十分なだけでなく必要でもある。
- **NO-GO**（証明済み。査読者が Carlson の条件を手で確かめた）。ある上限より下の $`R_2^C`$ から $`\le_2`$ の関係を 1 つ取り除いた構造は、[C11] の定理の仮定 (a)–(d) を満たし、いくらでも長い
  $`\le_2`$ の鎖と MIN と CC を持つが、その核には穴がある。だから (E) はこれらの仮定と MIN$`^S`$、CC$`^S`$ だけからは出ない。上の最初の穴についての結果は、これらと、点を動かす 1 つの補題しか使わない。
  「どの証明も $`\Sigma`$ 初等性が Carlson の条件について閉じていることを使わなければならない」という文は β0-CHAR によって同語反復なので、注意 (m3)。
- **$`\beta_0`$ のありうる場所**（場合分けとして証明済み）。$`x_F^C`$ より下の最初の食い違いの形は 2 つのどちらか：(N1) 2 つ目の条件が成り立つ、$`R_2^S`$ の穴の中の $`\alpha`$ の蓋、または (N2) $`\alpha`$ は
  $`R_2^S`$ で $`\lt_2`$ の後の点を持たず、そのとき $`\alpha \notin \mathrm{Core}(R_2^S)`$ で $`\sigma_S \le \alpha`$。SHARP-RIG から $`\beta_0 \ge x_F^C`$ を得るには、$`x_F^C`$ より下のどの上限でもそれが要る (m2)。
- **未証明**。(E)：未解決。査読者はちょうどの隙間を名指す：$`R_2^C`$ の核より下で、Carlson の条件が $`R_2^S`$ で与えるどの関係も $`R_2^S`$ で成り立たなければならない。$`x_F^C`$ より下ではこれは
  2 つ目の条件の固さで、$`L(\varepsilon+\omega^2)`$ から先のどの蓋でも場合 (N1) と (N2) を除くこと。$`\beta_0 \ge x_F^C`$：予想で、今は $`R_2^S`$ の中で述べた形。型 F は除かれていない。$`R_2^S`$ は計算できない
  ので、反例は探せない。概略だけ：最前線 $`L(\varepsilon\cdot\omega)`$、その先 $`L(\varepsilon_{\Phi_\Omega+2})`$。

### 1.3 素の符号：一般の段階の補題、木の単位、組の無い物

記号は [SHIFT8-ja.md](SHIFT8-ja.md) §2.3 と同じ：$`\Omega' = \Omega_{\omega+1}`$。段階 $`T`$ は札（$`\Omega_\omega`$ より下の順序数）の上の項で書き、その倍は $`\Omega_\omega\cdot T`$。

- **順序数の側、一般の補題**（証明済み。COVER と NAMES* の抽象的な芯は Lean で確かめた）。3 つの補題が、前の回の段階ごとの補題に置き換わる。GOOD-CRIT：$`T`$ の札の最大の段より
  上のどの段でも、$`T`$ が良いのは、$`\Omega_\omega\cdot T`$ の中でたどり着くどのつぶしの引数も $`\Omega_\omega\cdot T`$ より下であるときちょうど。COVER：$`\beta \lt \Omega_{j+1}`$ について、高々 $`\aleph_j`$ 個の倍
  $`\Omega_\omega\cdot T'`$（$`T' \lt T`$）が、$`\Omega_\omega\cdot T`$ より下にある閉包の部分を覆う。NAMES*：どの極限の段階 $`T`$ でも

```math
\psi_{\Omega_{j+1}}(\Omega_\omega\cdot T) = \sup\{\psi_{\Omega_{j+1}}(\Omega_\omega\cdot T') : T' \lt T,\ T' \text{ good at level } j\}.
```

  （右辺は、段 $`j`$ で良い $`T' \lt T`$ についての上限。）STEP も証明済み。査読者：「札無し」の決まりを 1 つに決める (m1)。分け方の項は Cantor の標準形の項に分けておく (m2)。
- **未証明：STAGE$`^G`$**（進行を止める点 B-1、たぶん直せる）。これらの補題を段階の系につなぐ一般の段階の補題は、それより前のすべての段階の中で上に限りなく続く集まりを使う。
  $`T`$ の札の段ではそうなっていない：査読者は段 1 の $`\varepsilon`$ 数の札を持つ反例を出した。もっと上の段では、そこで良くない前の段階の中で上に限りなく続くことが示されていない。前の回は
  これを具体的な鎖から得ていた。直し方の見込み：閉包の上限を大きくし、補題 BUMP（前のどの段階も、その倍がその閉包に入る前の段階より下にある）を示す。だから PUSH$`^G`$、「順序数の側は
  $`\theta_0`$ まで揃った」、下の 2 つの評価は証明されていない。
- **木の単位と組の無い物**（宿す補題は証明済みで、査読者は R1 のどの仮定も NEXT-HOST のどの場合も手で確かめた。REGION と SHAPE は移しで証明済み）。遺伝的な位置の値ごとに単位が
  1 つ、葉の値ごとに符号が 1 つで、どちらも値の順に並ぶ。新しい客は、そのすぐ上の宿主の単位での R1 で写す。上の部分の中の $`\Omega'`$ より上の原子（$`\Omega'`$ の上の Veblen の原子と
  $`\psi_{\Omega_{\omega+2}}`$ によるつぶし）には、加法的に主要な点を何個か持ち組を持たない物（重さ 2 と 3）。次の宿主の位置は写せる原子（NEXT-HOST、$`\varepsilon`$ の閉包による）。$`\Omega'`$ の単位は
  $`y`$ より上に組の無い万能の源を持つ。どの符号も鎖の数 3 のまま。細かい点：1 つの写しはある点より上に置く (m3)。1 つの閉包には札より上の点が要る (m4)。
- **未証明：評価**（STAGE$`^G`$ による）。素の符号で、$`\mathrm{CH}_4`$ について

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1}) \quad\text{(Conjecture TREE)},\qquad \iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+2}),
```

  と、$`\psi_{\Omega_1}(\Omega_{\omega+2})`$ までの $`\mathrm{CH}_4`$ での RED-TOWER。証明済みの素の評価は $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega'^2 + \psi'(\Omega'^2))`$ のまま（[SHIFT8-ja.md](SHIFT8-ja.md) §2.3）。物ごとに組を
  持たせても効くが、鎖の数が 4 になるので $`\mathrm{CH}_5`$（注意）。
- **その先**（未証明）。予想 MULT$`^n`$：どの $`n`$ でも $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+n})`$、だから $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ までの $`\mathrm{CH}_4`$ での RED-TOWER。組を積み重ねて鎖の数
  $`n+3`$ にする版：概略。引数の符号を添字にした $`\Omega`$ の単位：概略。注意：$`\Omega_{\omega\cdot 2+1}`$ より先では段階の集合がどの深さの入れ子のつぶしも含む（深さ 4 まで確かめた）ので、どちらの
  やり方も深さに限りの無い上端が要る。$`\theta_0`$ と「最初の扇は到達不能基数を要する」：未解決。

### 1.4 35 回目のあとの状態

- $`R_2^C`$ での Wilken の主張：FRAG 無しで $`[0, X_4]`$、そして **FRAG のもとで $`[0, L(G_2)]`$、$`L(G_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+G_2})`$** で両方の半分とも成り立つ（$`[0, X_{21}]`$ は
  査読 2 回。$`\nu_C = \nu_S = L(\omega+1)`$ までは査読 1 回と監査。$`\nu_C`$ から $`L(\omega^2)`$ までは査読 2 回。$`L(\omega^2)`$ から $`L(\Omega_1\cdot\omega)`$ までは査読 1 回。$`L(\Omega_1\cdot\omega)`$ から $`Z^+`$ までは
  査読 2 回。$`Z^+`$ から $`L(\varepsilon_{\Phi_\Omega+1})`$ までは査読 1 回、[SHIFT8-ja.md](SHIFT8-ja.md) §2。$`L(\varepsilon_{\Phi_\Omega+1})`$ から $`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$ までは査読 2 回で 2 つの証明、§1.1、§1.2。
  そこから $`L(G_2)`$ までは査読 1 回、§1.1）。
- $`R_2^S`$ での Wilken の主張：FRAG のもとで $`[0, L(\varepsilon_{\Phi_\Omega+1}+\omega^2))`$（§1.2）。FRAG 無しでは $`\upsilon_{\omega^3}`$ まで。
- $`R_2^S`$ と $`R_2^C`$：右端が $`L(G_2)`$ 以下のどの関係でも 2 つは一致する（FRAG のもと）。$`\beta_0 \ge \sigma_S`$ で、$`\sigma_S`$ は加法的に主要で $`[\rho(\beta_0), \beta_0]`$ にある。(E) は「2 つの核が
  等しい」と同値で、[C11] の仮定と MIN と CC だけからは出ない。$`\beta_0`$ の場所は分かっていない。
- 届く先（FRAG のもと）：$`L(G_2)`$ より下のどのやり直しでもちょうど。
- **LOW：FRAG のもとで偽**。**LOW$`^\infty`$：FRAG のもとで真**（どちらも査読 1 回。変化なし）。予想 CORE-2 の段階 PIN と LOW：決まっていない（変化なし）。
- $`\theta_0`$ より下の下からの評価の計画：素の評価 $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ と $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$（どちらも査読 1 回。変化なし：
  §1.3 の評価は STAGE$`^G`$ 待ち）。SRO より下の段階：変化なし（3,166 個の標本の行列すべてでどの $`n`$ でも。SRO より下のすべての標準の行列についての一般の命題は未解決）。

### 1.5 35 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。境目の定数を持つ 900 個の標準形の添字で定義域の判定、食い違い 0。ARG-BOUND。7 つの基での読みの点。71 個の行き先。目印の鎖。上に限りなく続く 3 つの塔。Lean は緑で
  Python と同じ。査読者：入れ子の $`\psi_{\Omega_2}`$、$`\psi_{\Omega_3}`$、$`\psi_{\Omega_4}`$ と繰り返した不動点の対照を持つ、別の文法の 1,500 個の添字で定義域の判定、食い違い 0、ARG-BOUND の失敗 0。
  $`\omega^{G_2} = G_2`$ なので $`L(G_2)`$ が正しい最前線。7 つの基での読みの点の順序。著者の実行と Lean のファイルの再実行は同じ出力。
- §1.2。19 個の添字で標準形と定義域、食い違い 0（3 つの対照は正しく失敗）。40 個の行き先、どれも正しい。目印の鎖は増える。査読者：著者の実行の再実行は同じ出力。$`\varepsilon`$ とその先の
  359 個の添字で定義域の判定、食い違い 0。63 個の行き先、どれも整合。$`L(\varepsilon)`$ の区域の鎖。それを確かめる Lean のファイル（緑で Python と同じ）。$`R_2^S`$、$`R_2^C`$、届く先、写像 $`f`$ は
  計算できない。
- §1.3。2 つの種でそれぞれ名前の 89 個の確かめ、失敗 0（査読者の再実行も同じ）。14 個のパターンで鎖の数は予想どおり。Lean のファイルは緑。証明書（再生した）：前向きの模型 5 個中 5 個が
  見つかり、逆向きは 3 個中 0 個。査読者：どの模型も新しい 1 つの物を 1 つの宿主の物に対して試すだけで、同じ種類の 2 つの物の場合と符号を持つ場合には証明書が無い (m5)。

### 1.6 未解決

- FRAG のもとで $`L(G_2)`$ より上の主張（FRAG 無しでは $`X_4`$ より上）。次は $`G_2`$ からの符号（区間全体を通しての相対的な遠い留め、そのあと 1 つ上の窓の規則）、骨組みの長いやり直しと
  その着地の計算、$`P_3`$ より下の符号、$`\nu_3`$。$`R_2^S`$ で：$`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$ より上の主張。FRAG 無しで $`\nu`$ より上の段の $`o_k = \omega`$。
- 2 つの段をまたぐ $`m^*`$ での越え方を、確かめの行つきの独立の段階として書くこと（[SHIFT8-ja.md](SHIFT8-ja.md) §1.2 の細かい点 m5）。
- $`L(G_2)`$ より上の $`R_2^S = R_2^C`$：(E)、つまり $`R_2^C`$ の核より下のどの蓋でも 2 つ目の条件の固さ（§1.2）、そして $`\beta_0`$ そのもの（予想：$`\beta_0 \ge x_F^C`$）。$`\kappa_C`$ より上の後続の段階での
  $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と $`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数：$`\varepsilon_{\Omega_\omega+1}`$ より先の鎖の数 3。補題 BUMP（§1.3 の B-1 の直し）で $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+2})`$ が出るはず。そのあと $`\Omega_{\omega\cdot 2}`$ までの MULT$`^n`$、
  引数の符号を添字にした $`\Omega`$ の単位、$`\Omega_{\Omega_1}`$、$`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。$`\nu`$ より上の、$`\upsilon`$ の点でない点の名前。
  [COVER-ja.md](COVER-ja.md) §9 の残り。
