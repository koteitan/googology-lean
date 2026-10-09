[← Back](README-ja.md) | [English](SHIFT6.md) | [Japanese](SHIFT6-ja.md)

# $`R_2^+`$ の 27 回目：FRAG のもとで $`\nu_C \ge X_{22}`$、$`G(\hat\zeta_3)`$ より下の長いちょうどの届く先、クッションの蓋、動く下の点のピン、$`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ までの素の符号

このページは [SHIFT5-ja.md](SHIFT5-ja.md) の続き（そこの §2 が 26 回目）。§1 が 27 回目。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことの言い直しにすぎないと言った結果は、進みとして数えない。

## 1. 27 回目

3 つの論文（2026-10）。どれも 1 回ずつ査読された。だからこの節の結果は、回数を書いていなければ査読 1 回。**査読 2 回** とは、26 回目の査読者が
直しを出した（またはその結果を確かめた）うえで、この回の査読者が書き出したものをもう一度確かめたもの。どの論文も Wilken, JSL 72 (2007)、
Carlson, AML 38 (1999)、Wilken, AML 45 (2006)、Carlson 2009, p. 97 が予告する同値を使わない。引く論文：§1.1 で [W07b]（L.2.1、Thm 2.2、Thm 5.3 の証明）。
§1.2 と §1.3 の証明済みの段階はどの論文も使わない（§1.3 は注意の中で Carlson 2001 を引くだけで、FRAG も使わない）。Lean のファイルは足していない：
§1.1 と §1.3 の論文は項を比べるだけの Lean のファイルを確かめた（`#eval`、定理は無い。緑で、査読者の再実行でも緑）。これらは確かめた扱い。§1.2 には Lean のファイルは無い。
26 回目の査読の細かい点（[SHIFT5-ja.md](SHIFT5-ja.md) §2）は反映した：そこの §2.1 へのものは §1.1 の論文が、§2.2 へのものは §1.2 が、§2.3 へのものは §1.3 が反映し、
その査読者がもう一度確かめた（**査読 2 回**）。段の番号は [SHIFT-ja.md](SHIFT-ja.md) と同じ（論文より 1 つ大きい）：段 1 は $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ より下で、
段 $`1+\xi`$ はやり直し $`H(\Omega_\omega\cdot\xi + \eta')`$（$`0 \lt \eta' \lt \Omega_\omega`$）からなる。

[SHIFT5-ja.md](SHIFT5-ja.md) の名前：$`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$、$`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$、$`G_2 = G(\omega^2)`$、$`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$、$`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$、
$`\hat\zeta_3 = \theta_3\cdot\omega^2`$、$`\hat\zeta_G = \theta_3\cdot\Omega_3`$、$`\hat\zeta_A`$、$`\hat\zeta_H`$、$`\hat\zeta_f`$、$`\hat G = G(\Omega_2)`$、$`F_\lambda = H(\eta_\lambda + \Omega_1)`$、読み方 $`R`$、$`u_4 = H(\Omega_4)`$、$`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$。
この回の新しい名前：

```math
\theta_4 = \psi_{\Omega_5}(\Omega_\omega),\qquad \mathrm{st}(T) = \psi_{\Omega_1}(\Omega_\omega\cdot T).
```

$`R(\theta_4\cdot\omega^2) = G(\hat\zeta_3)`$、$`\hat\zeta_H \lt \Omega_4 \lt \theta_4\cdot\omega^2 \lt \Omega_5`$、$`G(\hat\zeta_3) \lt G(\Omega_4) \lt G(\theta_4\cdot\omega^2) \lt P'`$（確かめた）。$`\mathrm{st}^n`$ は $`\mathrm{st}`$ を $`n`$ 回重ねたもの。

### 1.1 添字 $`\theta_2+1`$ より先の PSI-θ、$`G(\hat\zeta_3)`$ より下の長いちょうどの届く先、クッションの蓋：FRAG のもとで $`\nu_C \ge X_{22}`$

- **[SHIFT5-ja.md](SHIFT5-ja.md) §2.1 への査読の細かい点を反映した**（証明済み、**査読 2 回**）。THETA$`^G`$ の段階「上限は $`F_\lambda`$ 以下」は今は査読者の帰納法。
  非可算の乗数での形には高い部分つきの PSI-n と符号の覆いの補題を引き、「上へ」は $`\pi_\eta`$ より下でだけ言う。読み方は包の中に留まる。EXACT-LONG$`^G`$ と EXACT-F の行き先は
  TOP-REG-LAND から取る。$`\hat\zeta_A`$ での天井は証明済み。NO-READL は EXACT-LONG$`^G`$ と EXACT-F に立つ。蓋の値は「着地の最大」という注意の読み方によらない。
  だから FRAG のもとでの $`[0, X_{21}]`$ での主張は今は **査読 2 回**。
- **PSI-θ$`^{(3)}`$**（移しで証明済み）。$`\psi_{\Omega_2}`$ の数える規則は、$`\zeta_H`$ が $`\hat\zeta_G`$ より下の $`\Omega_3`$ の倍数で $`\delta \lt \Omega_3`$ のどの標準形 $`\psi_{\Omega_2}(\Omega_\omega + \zeta_H + \delta)`$ でも成り立つ：
  1 つ下の段での PSI-n と同じ証明を、査読済みの $`\psi_{\Omega_3}`$ の数える規則の上で行う。だから規則 PSI-θ は今は添字 $`\theta_2+1`$ で成り立ち（26 回目には無かった）、
  $`\psi_{\Omega_3}(\Omega_\omega + \hat\zeta_G)`$ より下のどの添字でも成り立つ。$`\hat\zeta_G`$ より下のどの正規の乗数 $`\zeta`$ でも、$`G(\zeta+1)`$ は規則の類 $`C_{\theta_2}`$ で $`G(\zeta)`$ の次の元で、
  だから $`[G(\zeta), G(\zeta+1))`$ のどの符号も基 $`G(\zeta)`$ の上の形を持つ。
- **THETA$`^{(3)}`$、EXACT-LONG$`^{(3)}`$、MONO-L$`^{(3)}`$、LAND-B**（移しで証明済み、FRAG のもと）。素の読み方 $`\Theta_\lambda`$ を $`G(\hat\zeta_3)`$ より下の（$`\pi_{\eta_\lambda}`$ より下の）どの符号でも定義する。
  それらを $`[0, H(\eta_\lambda + G_2))`$ の上へ写し、移しと入れ替えられ、$`\Theta_\lambda(G(\zeta)) = H(\eta_\lambda + 1 + R^\Theta_\lambda(\zeta))`$（$`R^\Theta`$ は定数を $`\Theta_\lambda`$ で読んだ読み方。基 $`\hat G`$ での読み方を
  $`F_\lambda`$ で読むのは $`\zeta = \Omega_2`$ の場合）。だから符号 $`G_2\cdot D + m_0`$ の長いやり直しの届く先は、どの $`D \lt G(\hat\zeta_3)`$ でもちょうど分かる（前は $`D \le \hat G`$）。着地の η のずれは
  $`G_2`$ より下で、短い前置きしか持たないので、越えは起きない。届く先は符号について狭義に増え、$`G(\hat\zeta_3)`$ より下の符号のどのやり直しも $`H(\eta + G_2)`$ より下に届く。
  （査読者：論文は LAND-B の上限を「$`+1`$」で書くが、書いたままでは偽。「$`+\omega^2`$」ならどの使い方でも成り立つ。）
- **FAR-PIN$`^{L3}`$、OWN-PREFIX$`^f`$**（移しで証明済み、FRAG のもと）。$`G(\hat\zeta_3)`$ より下のどの符号も、遠いピンのためのちょうどの原子。$`\hat\zeta_f`$ では、やり直し自身の符号 $`\hat G + G_2`$ の前置きが
  $`\Omega_1 + \omega^2`$ だけ先に着地するので、READ$`^L`$ はこの前置きによってもそこで成り立たず、包の蓋 CAP$`^\sharp`$ はその族で成り立つ。（査読者：$`\hat\zeta_H`$ での極限の段階を書き出すこと。）
- **CUSHION**（移しで証明済み、FRAG のもと）。包の要らない蓋。$`\lambda`$ を符号 $`m`$ が $`[G(\zeta), G(\zeta+1))`$ にあり $`G(\hat\zeta_3) \le m \lt G(\theta_4\cdot\omega^2)`$ のやり直しとし、$`C`$ を $`R_\lambda(\zeta)`$ の
  指数が $`G_2`$ 以上の項の和に $`G_2`$ を足したものとする。[SHIFT2-ja.md](SHIFT2-ja.md) §2.1 の蓋の読み方 $`\Phi_\lambda`$ で：

```math
r(\lambda) \lt H(\eta_\lambda + C + \omega^2\cdot\Phi_\lambda(m) + \omega^2).
```

  $`G(\hat\zeta_3)`$ より下の符号の着地はどれも、自分の前置きから $`G_2`$ 未満しか先に行かないので、項 $`G_2`$ がどの越えも吸い込み、$`\omega^2\cdot\Phi_\lambda(m)`$ が符号を分ける。
  （査読者：ここでも論文は「$`+\omega^2`$」を「$`+1`$」と書く。算術の補題の「前置き」は「真の前置き」とすること。）
- **系**（移しで証明済み、FRAG のもと）。**$`G(\theta_4\cdot\omega^2)`$ より下のどの符号でも CAP-0**（前は $`G(\hat\zeta_H)`$ より下）：$`[\Omega_3, \Omega_4)`$ のどの乗数も、台の頂上 $`u_4`$ も、
  $`[\Omega_4, \theta_4\cdot\omega^2)`$ の乗数も含む。**$`u_4`$ は自分を越えない**。仮定は要らないので、DICHOTOMY-4″ の場合 (ii) は起きない。LONG-CLASS$`^{22}`$：$`r(\lambda) \ge H(\eta_\lambda + G(\hat\zeta_3))`$ なら
  $`m_\lambda \ge G(\theta_4\cdot\omega^2)`$。LOW-RED$`^{22}`$：LOW$`_x`$ なら、$`x`$ より下に、符号が $`[G(\theta_4\cdot\omega^2), P')`$ にある自分を越える長いやり直しが共終に多くある。
- **定理 X22**（証明済み、FRAG のもと）：

```math
\nu_C \ge X_{22} = \psi_{\Omega_1}(\Omega_\omega + \theta_4\cdot\omega^2 + \omega^{G(\theta_4\cdot\omega^2)+1}\cdot 2),\qquad G(\theta_4\cdot\omega^2) = \psi_{\Omega_2}(\Omega_\omega + \theta_4\cdot\omega^2).
```

だから **FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, X_{22}]`$ で両方の半分とも成り立つ**。$`\nu_S \ge X_{22}`$、$`X_{21} \lt u_4 \lt X_{22}^- \lt X_{22}^\natural \lt X_{22} \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$（Python と Lean で確かめた）。
新しい道具の一部だけでは、同じ証明が代わりの点 $`X_{22}^\natural`$ と $`X_{22}^-`$ を与える：$`\theta_4\cdot\omega^2`$ をそれぞれ $`\Omega_4 + \psi_{\Omega_4}(\Omega_\omega + \Omega_4)`$ と $`\Omega_4 + \theta_3`$ に替えたもの。また（P-LOW$`^{22}`$）
$`H(\theta_2\cdot\omega^2) \lt a \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ で $`(a, b)`$ に (P) があるどのやり直し $`a`$ も $`m_a \ge G(\theta_4\cdot\omega^2)`$。（査読者：1 つの段階で、CUSHION の区域の仮定がそこで成り立つことを
書くこと。）**仮定つき。数えない**：LOW が偽なら $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\theta_4\cdot\omega^2)+1})`$。

- **未証明**（進行を止める点。X22 はこれを使わない）：EX-RED「$`G(\Omega_k)`$ より下のどの符号にもちょうどの原子があれば $`G(\Omega_{k+1})`$ より下で CAP-0」、またそれによる
  「$`P'`$ より下のどの符号にもちょうどの原子があれば LOW は偽」。証明は $`G_2`$ の代わりに $`\omega^{G(\Omega_{k-1})+1}`$ を置く。するとクッションの最後の項の符号は $`G(\Omega_{k-1})+1`$ で、その着地の
  ずれは非可算（$`k = 4`$ で $`Z`$）なので、その原子はどの行き先の候補よりも上にある（査読者の試し）。査読者の出す直しの候補（確かめていない）：仮定を「着地は $`R(\zeta) + \Omega_1`$ より下」と
  強め、クッションの項を $`\omega^{Z+1}`$ まで下がる有限の列で終えること。
- **未解決**：クッションが止まるところ。$`\theta_4\cdot\omega^2`$ で読み方は $`G(\hat\zeta_3)`$。$`\theta_4\cdot\omega^2 + \omega^{\psi_{\Omega_3}(\Omega_\omega + \theta_4\cdot\omega^2)+1}`$ まではあらすじでクッションが延びる。分ける原子の無い
  最初の符号は $`G(\hat\zeta_3) + 1`$：そこでは着地の蓋は上からの評価しか与えず、合う下からの評価（EXACT-LAND）は未解決。$`G(\hat\zeta_A)`$ からの両側の包の蓋、$`\Omega_k`$（$`k \ge 5`$）と
  $`\Omega_\omega`$ でのそれ：未解決。LOW：未解決。
- 査読者のほかの細かい点：天井から $`\eta \ge \theta_2\cdot\zeta`$ への段階にはもう 1 行要る。論文の札「証明済み（障害）」は「注意」とすること。1 つのスクリプトの説明文が古い。

### 1.2 $`\nu_C = \nu_S`$：動く下の点のピン、$`\varepsilon_{\hat G+1}`$ より下のどの符号でも基の取りかえ

記号は [SHIFT5-ja.md](SHIFT5-ja.md) §2.2 と同じ。LOW$`^\infty`$ は $`\nu_C \lt \upsilon^\infty`$。

- **[SHIFT5-ja.md](SHIFT5-ja.md) §2.2 への査読の細かい点を反映した**（証明済み、**査読 2 回**）：前の道の進行を止める点は、取り除かれたのではなく LOW$`^\infty`$ に置き換わった。
  θ の層の蓋と移しのひな形について照合の行を書き、η による場所はどれも知られた 6 つの種類のどれか（査読者は 3 行を抜き取りで確かめた）。段をまたぐ基の取りかえの
  抜けた場合。符号 0 はやり直しを与えない。EXACT-CL\* のついでの直し（[SHIFT4-ja.md](SHIFT4-ja.md) §2.1）。
- **BC$`^{\mathrm{mv}}`$、THETA-EQ$`^{\mathrm{mv}}`$、MRC$`^{\mathrm{mv}}`$、PIN-ALL$`^{\mathrm{mv}}`$、LPIN$`^{\mathrm{mv}}`$**（証明済み、FRAG のもと。[SHIFT5-ja.md](SHIFT5-ja.md) §2.2 の進行を止める点の直し）。ピンは、像がどの
  やり直しでもよく、下の引数が動き、そこでは $`h \ge T`$ しか分からない基のやり直し $`\nu`$ でも働く：最初の段階は遠いピン（PIN-IDX ではない）、動く下の原子は $`h \ge T`$ で扱い、
  帰納法はずれについて回す。だから長い前置きの着地のやり直しは、その符号が動く区域に原子を持っても、どの $`D \lt \varepsilon_{\hat G+1}`$ でもピンで留まる。
  （査読者：鍵の段階には査読済みの前例 [SHIFT5-ja.md](SHIFT5-ja.md) §1.1 の FAR-PIN$`^L`$ がある。動く集合はカントール標準形の項と指数について閉じていること。基の添字の指数が
  大きいという仮定を書くこと。ただ 1 つの使い方ではそれは成り立つ。）
- **制限無しの PIN$`^{(2)}`$**：**書いたままでは未証明**（論文は前のピンの補題が書いたまま成り立つと言うが、その証明には原子の受け継いだ引数でも $`h \ge T`$ が要る）。
  **仮定つき。数えない**（LOW$`^\infty`$ のもとで、FRAG のもとで正しい）：その仮定を同時の帰納法で出せば、TOP-REG$`^{T2}`$、PLACE$`^{T2}`$、RES-ALL$`^{T2}`$ と
  [SHIFT5-ja.md](SHIFT5-ja.md) §2.2 の帰着は、原子に制限無しで成り立つ。
- **26 回目の道具をどの段でも**（移しで証明済み、FRAG のもと）：THETA$`^G`$、EXACT-LONG$`^G`$、EXACT-F、$`G(\hat\zeta_H)`$ より下の着地の蓋と包の蓋、LONG-CLASS$`^{21}`$ は
  どの段 $`\ge 1`$ でも成り立つ。
- **THETA$`^e`$、EXACT-LONG$`^e`$、TC⁺$`^e`$、MONO-F$`^e`$**（証明済み、FRAG のもと）。$`G_2\cdot\hat G = \hat G`$ なので、EXACT-LONG$`^G`$ と EXACT-F が含むのは $`\hat G + G_2`$ より下の符号だけ。新しく：
  $`\hat G`$ の上のカントール標準形を $`F_\lambda`$ で読む。どの $`D \lt \varepsilon_{\hat G+1}`$ でも長いやり直しは η のずれ $`\Omega_1 + x`$（$`x`$ は可算）に着地し、届く先はちょうど分かる。どの段のやり直しの間の
  どの基の取りかえ $`B`$ でも、符号が $`\varepsilon_{\hat G+1}`$ より下のどのやり直し $`R`$ でも $`r(BR) = B(r(R))`$。だから **届く先は、$`\varepsilon_{\hat G+1}`$ より下のどの符号でも、どの段でも、基の取りかえと
  入れ替えられる**（前は $`G_2^2`$ より下）。（査読者：「上へ」には $`\pi_\eta \gt \hat G`$ が要る。段 1 の $`\pi_\eta \lt \hat G`$ のやり直し、たとえば $`\eta = \omega^2`$ では成り立たない。どの使い方でも符号は $`\hat G`$ 以上。）
- **仮定つき。数えない**（LOW$`^\infty`$ のもとで、FRAG のもとで正しい）：どの段でも $`G(\hat\zeta_H)`$ より下の READ$`^\sharp`$ を使えば、底の符号が $`G(\hat\zeta_H)`$ より下の (D1b) のまたぎと、
  η のずれが $`\varepsilon_{\hat G+1}`$ より下のまたぎはどれも置ける。余地は $`G(\hat\zeta_H)`$ より下のずれに届く。区域は $`H(\eta_u + \varepsilon_{\hat G+1})`$ になる。TWIST のあとの点検は、今は 1 行ずつ
  書かれ、成り立つ（査読者：1 つの使い方「区域が次の点より下にある」は区域の公理ではないが、ここでは成り立つ）。
- **REDUCTION$`^{(4)}`$**（仮定つきの命題として証明済み）。$`\nu_C = \nu_S`$ は FRAG、LOW$`^\infty`$ と 3 つの未解決のものから出る：(R1″) $`[\varepsilon_{\hat G+1}, \Omega_2)`$ の符号と
  $`\tau \ge \Omega_2`$ のやり直しでの、ちょうどの着地の届く先（$`\hat G`$ の上のヴェブレンの層はあらすじだけ）。(R2″) $`G(\hat\zeta_H)`$ 以上の符号での蓋（η のずれが $`G(\hat\zeta_H)`$ 以上のまたぎでだけ要る）。
  (R5) $`H(\eta_x + G(\hat\zeta_H))`$ より先の区域（新しい）。TWIST のあとの点検はもう入力ではない。$`\nu_C = \nu_S`$ も $`\nu_C \lt \nu_S`$ も **未解決**。
- 査読者のほかの細かい点：$`G(\Omega_3+1)`$ より下の符号には READ$`^\sharp`$ ではなく LONG-CLASS$`^{21}`$ の蓋の節が要る。1 文は重複。著者の着地のずれの試しは $`F`$ より下のずれだけで、
  査読者の試しが $`F`$ から作ったずれを含む。

### 1.3 素の符号：下の符号をまるごと段階の札に使う、$`\sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$

言葉は [SHIFT3-ja.md](SHIFT3-ja.md) §1.2、§1.3 と [SHIFT5-ja.md](SHIFT5-ja.md) §2.3 と同じ：段階、組のブロック、鎖の数、飾り、モジュールの系。

- **[SHIFT5-ja.md](SHIFT5-ja.md) §2.3 への査読の細かい点を反映した**（**査読 2 回**）：始めの段階では各 $`Z_n`$ より下の系を 1 つずつ使う。写した札の運び手は大きいほうの札の点 $`p`$ で、
  写しは $`b`$ より上にある。重みは外し、古い元と新しい元を合わせたものが閉じていることを書いた。2 つ目の組は「要らない」。$`\mathrm{CH}_3`$ と $`\mathrm{CH}_4`$ の比較は HOST$`_4`$ を引く。
  Carlson 2001 は同一視を予告するだけ。
- **どの可算の段階でも順序数の側**（移しで証明済み）。$`\Omega_\omega`$ を基とする $`\psi`$ の数える規則と [SHIFT3-ja.md](SHIFT3-ja.md) §1.2〜§1.3 の引数の補題は、どの可算の段階 $`T`$ でも成り立つ。
  いちばん下の段では引数の補題は片方の向きだけで成り立ち、使うのはその向きだけ（査読者：もう片方の向きは、たとえば $`T = \varepsilon_0`$ で成り立たない）。
- **BELOW-σ、FIX-σ、PUSH$`^S`$**（証明済み）。$`T_1 = \varepsilon_0`$、$`T_{m+1} = \mathrm{st}(T_m)`$ とすると $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1) = \sup_m T_m`$ で、これは $`\mathrm{st}`$ の最小の不動点（査読者は閉包の Lean の
  定義と、構成子 1 つずつ照らし合わせた）。
- **REGION$`^M`$、SHAPE$`^M`$、STAGE-TOWER**（証明済み）。段階の札は下のモジュールの系の符号まるごと。組のブロックの組 $`a \lt_2 b`$ の中では、小さい札の写しが大きい札の点 $`p`$ より下にあり、
  $`p`$ がその運び手なので、段階の符号の隙間の問題は消える。パターンは扇を持たない。組の中の札は自分の鎖のほかに輪を足さないので、鎖の数 $`k'`$ の下の系から
  鎖の数 $`\max(3, k'+1)`$ の系ができる（札を $`b`$ より上に置くと $`k'+2`$）。
- **LADDER**（証明済み）。素の符号で、$`\Theta_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$ として：

```math
\iota(\mathrm{CH}_k) \ge \mathrm{st}^{k-2}(\Theta_1)\ (k \ge 2),\qquad \iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1),\qquad \sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1).
```

  前は $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$。札を $`b`$ より上に置くだけでも $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1)`$ が出る（組の中に置くことが退けられたときの代わりの道）。
  だから RED-TOWER は素の符号で、$`t`$ とともに増える鎖の数で、$`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ より下のどの $`t`$ も含む。$`\varepsilon_0`$ より先の組の無い区域の符号は要らない。
- **未解決**：$`\xi \ge \Omega_1`$ の札（段階の添字が引数を持ち、順序数の側はまだそれを扱えない。そのような札の素の側はあらすじだけ）。$`\Omega_\omega`$ 以上の札と $`\Omega`$ の塔。
  $`\mathrm{st}(Z_\omega)`$ より先での鎖の数 3。$`\theta_0`$ ははるか上。
- 査読者のほかの細かい点：論文は 2 つの写像に 1 つの文字を使う。素の側の隙間が消えたという見出しの主張は、符号を持つ札でだけ成り立つ。記録の評価は下からの評価。
  2 つの頂上の予想した比較の 1 つは補題が含まない。$`\pi \gt \Omega_1`$ で $`\psi_\pi(e) \gt \Omega_1`$ という 1 行を足すこと。

### 1.4 27 回目のあとの状態

- $`R_2^C`$ での Wilken の主張：$`[0, X_4]`$ では FRAG 無しで、$`[0, X_{22}]`$ では FRAG のもとで（$`[0, X_{21}]`$ は査読 2 回）両方の半分とも成り立つ。核の側は $`[0, \nu_C]`$ で成り立つ。
  $`\nu_C`$ の InaccPsi による上からの評価は無い：名前の付いた組での (P) は未解決のまま。
- 届く先：$`\tau \lt G_2`$ のどの短いやり直しと、段 1 で符号が $`G(\hat\zeta_3)`$ より下のどの長いやり直しでもちょうど分かる（FRAG のもと）。基の取りかえつきでは、どの段でも
  $`\varepsilon_{\hat G+1}`$ より下のどの符号でも。$`G(\theta_4\cdot\omega^2)`$ より下のどの符号でも CAP-0。
- 名前：変わらず（$`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ より下のどの $`\upsilon`$ 点も名前 $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ を持つ）。
- $`\theta_0`$ より下の下からの評価のための計画：SRO より下の段は、標本の 3,166 個すべてですべての $`n`$ で成り立つ（変わらず）。素の符号で $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1)`$、
  $`\sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$、$`\iota(\mathrm{CH}_2) \ge \Theta_1`$。
- 上からの評価：$`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ の InaccPsi の項による評価はまだ無い。
- $`\nu_C = \nu_S`$：LOW は決まっていない。$`u_4`$ は自分を越えない。動く原子のあるピンは直った。残り：LOW$`^\infty`$、(R1″)、(R2″)、(R5)。

### 1.5 27 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。PSI-θ$`^{(3)}`$ の規則のデータ。項の順序に対する規則の試し 2 × 49,506 組で食い違い 0（わざと間違えた規則では 67）。種ごとに約 360 個の正規の乗数でクッションの余白、
  失敗 0。$`\theta_4\cdot\omega^2`$ での天井を標本 1,067 個で。名前、標準形、鎖 $`X_{21} \lt u_4 \lt X_{22}`$ を Python と Lean で（緑、同じ出力）。査読者：高い部分を $`\hat\zeta_G`$ まで広げた規則の試しを
  種ごとに 16,512 組（種 2 つ）で、食い違い 0（壊した規則では 18）。$`\theta_4\cdot\omega^2`$ の近くのクッションを乗数 125 個で、次の元の規則を 237 個で、失敗 0。EX-RED の証明を否定する試し。
  Lean の再実行は同じ。
- §1.2。順序、所属、着地のずれ、上限、$`\hat G`$ の上の層（5 つの試し、失敗 0）。査読者：著者の試しの再実行は同じ出力。自前の試し 15 個中 15、150 個中 150、30 個中 30。
  段 1 で $`\pi_\eta \lt \hat G`$ のやり直しを見つける試し。
- §1.3。名前、所属、FIX-σ の乱択の試し、失敗 0。札のブロック 34 個は扇の無いパターンで、鎖の数は 2（中）と 3（上）。Lean は緑。証明書（再生した）：前向き 14 個中 10 個、
  $`\mathrm{CH}_k`$ より下の頂上 4 個中 1 個、逆向き 6 個中 0 個（証明済みのものはこれに頼らない）。査読者：著者の実行はバイト単位で同じ、証明書 3 個を再生、Lean は緑で同じ出力。
  自前の項 46,356 個で、予想の上限より上のものは無い。34 個のブロックを自前の検査器で、誤り 0。

### 1.6 未解決

- 上からの評価：$`\nu_C`$ について名前の付いた 1 つの組での (P) と (Q′)。(P) には $`G(\theta_4\cdot\omega^2)`$ より先の蓋と、符号 $`P'`$ での下からの評価が要り、(Q′) には $`L(\omega)`$ の等最小の
  パターンが要る。$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価。
- FRAG のもとで $`X_{22}`$ より上の主張：符号 $`G(\hat\zeta_3) + 1`$ からのちょうどの着地の届く先。$`G(\hat\zeta_A)`$ からの、$`\Omega_k`$（$`k \ge 5`$）と $`\Omega_\omega`$ での両側の包の蓋。EX-RED（証明は
  クッションの最後の項で壊れる）。$`\Omega_3`$ より上の層の下からの評価の側。
- 最初の到達不能基数：$`\Omega_1`$ 以上の段階の札（引数を持つ段階の添字）、$`\Omega_\omega`$ 以上の札、$`\mathrm{st}(Z_\omega)`$ より先での鎖の数 3。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。
  SRO より下のすべての標準形の行列での段。
- $`\nu_C = \nu_S`$：LOW（符号が $`[G(\theta_4\cdot\omega^2), P')`$ での CAP-0）。LOW$`^\infty`$。(R1″)、(R2″)、(R5)。そのあと (D1b) と (E4)。
- 名前：$`R(\Theta_{d\omega})`$；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ；届く先を符号で書く InaccPsi の式；$`X_{22}`$ より先の名前；
  [COVER-ja.md](COVER-ja.md) §9 の残り。
