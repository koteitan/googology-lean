[← Back](README-ja.md) | [English](SHIFT5.md) | [Japanese](SHIFT5-ja.md)

# $`R_2^+`$ の 25 回目と 26 回目：FRAG のもとで $`\nu_C \ge X_{21}`$、着地の蓋と包の蓋、最初の添字の不動点までの長いちょうどの届く先、どの段でも TC⁺、どの η でも GEN、$`\psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$ までの素の符号

このページは [SHIFT4-ja.md](SHIFT4-ja.md) の続き（そこの §2 が 24 回目）。§1 が 25 回目、§2 が 26 回目。27 回目から 29 回目は [SHIFT6-ja.md](SHIFT6-ja.md)、30〜32 回目は [SHIFT7-ja.md](SHIFT7-ja.md)、33 回目と 34 回目は [SHIFT8-ja.md](SHIFT8-ja.md)、35〜37 回目は [SHIFT9-ja.md](SHIFT9-ja.md) にある。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことの言い直しにすぎないと言った結果は、進みとして数えない。

## 1. 25 回目

3 つの論文（2026-10）。どれも 1 回ずつ査読された。だからこの節の結果は、回数を書いていなければ査読 1 回。**査読 2 回** とは、24 回目の査読者が
直しを出した（またはその結果を確かめた）うえで、この回の査読者が書き出したものをもう一度確かめたもの。どの論文も Wilken, JSL 72 (2007)、
Carlson, AML 38 (1999)、Wilken, AML 45 (2006)、Carlson 2009, p. 97 が予告する同値を使わない。ここで引く論文：[SHIFT4-ja.md](SHIFT4-ja.md) §1 と同じ [W07a]（L.3.30、L.4.7）
と [W07b]（L.2.1、Thm 2.2、Def 4.1、Thm 5.3 の証明）。Lean のファイルは足していない：2 つの論文（§1.1、§1.3）が項を比べるだけの Lean のファイルを確かめ（`#eval`、定理は無い。
緑で、査読者の再実行でも緑）、§1.2 の査読者も同じ種類のものを書いた（緑）。これらは確かめた扱い。24 回目の査読の細かい点は反映した：[SHIFT4-ja.md](SHIFT4-ja.md) §2.1 と §2.2 へのものは
§1.1 の論文が反映し、その査読者がもう一度確かめた（**査読 2 回**）。そこの §2.4 のラベルの点は §1.3 が片づけた。残りは [SHIFT4-ja.md](SHIFT4-ja.md) §2 に反映した。段の番号は
[SHIFT-ja.md](SHIFT-ja.md) と同じ（論文より 1 つ大きい）：段 1 は $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ より下。

記号は [SHIFT4-ja.md](SHIFT4-ja.md) と同じ：$`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$、$`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$、$`G_2 = G(\omega^2)`$、$`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$、
$`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$、そこの §2.2 の読み方 $`R`$、$`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$。この回の新しい名前（[SHIFT4-ja.md](SHIFT4-ja.md) §2.2 の $`\hat\zeta_2`$ とともに）：

```math
\hat\zeta_3 = \theta_3\cdot\omega^2,\quad g_3 = \psi_{\Omega_3}(\Omega_\omega + \hat\zeta_3),\quad \varepsilon_+ = \varepsilon_{G_2+1},\quad \hat\zeta_4 = \hat\zeta_3 + \omega^{\omega^{g_3\cdot 2}},\quad \hat\zeta_\varepsilon = \hat\zeta_3 + \varepsilon_{g_3+1}.
```

$`R(\hat\zeta_3) = G_2`$、$`R(\hat\zeta_4) = \omega^{G_2^2}`$、$`R(\hat\zeta_\varepsilon) = \varepsilon_+`$、$`\hat\zeta_2 \lt \hat\zeta_3 \lt \hat\zeta_4 \lt \hat\zeta_\varepsilon \lt \Omega_4`$（確かめた）。

### 1.1 着地の蓋：FRAG のもとで $`\nu_C \ge X_{19}`$

- **[SHIFT4-ja.md](SHIFT4-ja.md) §2.1 と §2.2 への 24 回目の査読の細かい点を反映した**（証明済み、**査読 2 回**）。その中に：$`X_{18}`$ の証明の間違った段階を、最小の倍数の補題
  （$`e' \le e`$ なら、$`\gamma`$ より上の $`\omega^e`$ の最小の倍数は $`\ge \gamma + \omega^{e'}`$）で置き換えた。基 $`\eta \ge \Omega_2\cdot a`$ での D-UNC$`^{\mathrm{SEG}}`$（使っていたのに書いていなかった場合）。
  読み方の後者の段階を数える規則 PSI-n から導いた。尾の基を $`H(\Omega_3)`$ より上にとる。$`\tau_{\mathrm{LH}}`$ で分離しないという主張は注意にすぎない（下を見よ）。だからこれらの直しを入れた
  $`X_{17}`$ と $`X_{18}`$ の証明は **査読 2 回**（§1.2 の査読者も $`X_{18}`$ の証明の最後の段階をやり直した）。
- **CROSS-SHARP$`^{(3)\prime}`$**（移しで証明済み、FRAG のもと）。定数の無い正規の $`M \in [\Omega_3, \hat\zeta_3]`$ で：$`m_\lambda \ge G(M)`$ なら $`r(\lambda) \ge H(\eta_\lambda + R(M))`$。逆は
  $`R(M)`$ が $`\Omega_1`$ の倍数である $`M \in [\Omega_3, \hat\zeta_\varepsilon]`$ で成り立つ。これは [SHIFT4-ja.md](SHIFT4-ja.md) §2.2 の鋭い形を、そこの査読者が求めたとおりに制限したもの。（査読者：実現の帰納法が
  段によらないことを 1 行足すこと。）
- **SEP$`^{\mathrm{near}}`$**（証明済み、FRAG のもと）。$`G_2`$ より下のどの符号 $`c`$ にも分離するピンがあり、その原子は EXACT-CL\* が与える届く先。だから [SHIFT4-ja.md](SHIFT4-ja.md) §2.2 で
  足りなかった指数 $`\tau_{\mathrm{LH}} + 1`$ でのピンはある：$`\tau_{\mathrm{LH}}`$ と $`\tau_{\mathrm{LH}} + 1`$ での届く先は $`\varphi(\omega, \delta+1)\cdot\omega`$ と $`\varphi(\omega, \delta+1)\cdot\omega + 1`$。
- **$`G(\hat\zeta_3)`$ より下の蓋**（移しで証明済み、FRAG のもと）。$`\min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ より下で $`G(\Omega_3+1) \le m_\lambda \lt G(\hat\zeta_3)`$ のどのやり直し $`\lambda`$ でも $`r(\lambda) \lt H(\eta_\lambda + \Xi_\lambda + \omega^2)`$。
  ここで $`\Xi_\lambda`$ は読み方の蓋のずれで、ブロックの番号は最後のピンの原子のブロックより上にとる。だから $`G(\hat\zeta_3)`$ より下で CAP-0。（査読者：論文はこれを READ の文字どおりの
  蓋と呼ぶが、その蓋の細かい形（ブロックの番号を $`\ge 2`$ の最小にとるもの）は $`\hat\zeta_3`$ より下の $`M = \theta_3\cdot(\omega\cdot 2+1)`$ ですでに偽。証明されたのは上の粗い蓋。
  細かい形に頼る結果は無い。）
- **NO-LIT、LAND-LB**（証明済み、FRAG のもと）。$`\hat\zeta_3`$ では、行き先を最後の前置きのやり直しの区域に置く蓋は**偽**：$`\lambda = H(\hat\zeta_3)`$ の符号は $`G(\hat\zeta_3)`$ で、
  $`r(\lambda) \ge r(H(\hat\zeta_3 + G_2)) \ge H(\hat\zeta_3 + G_2 + \omega^2)`$。一般に、長いやり直し $`\nu`$ に届くやり直しは $`r(\nu)`$ に届き、それは $`\nu`$ の区域の先にある。これは [SHIFT4-ja.md](SHIFT4-ja.md) §2.2 の
  進行を止める点（$`G_2`$ より上では要る形の分離が無い）を正確にしたもの。
- **THETA⁺、EXACT-LONG⁺**（移しで証明済み、FRAG のもと）。符号 $`G_2\cdot D + m_0`$、$`D \lt \varepsilon_+`$、$`m_0 \lt G_2`$ の長いやり直し $`\lambda`$ の届く先はちょうど分かる：添字の距離
  $`\omega^2\cdot\Theta^+(D)`$ に着地する。ここで $`\Theta^+`$ は $`\varepsilon_+`$ より下の符号の順序同型で、移しと入れ替えられる。前は $`D \lt G_2`$ で長いやり直しのちょうどの届く先が分かっていた。
- **FAR-PIN$`^L`$、MULTI-RC$`^L`$、TOP-REG-LAND**（移しで証明済み、FRAG のもと）。長い前置きのやり直しは、着地の区域にあるその原子を通してピンで止まる（入れ子のピン）。これで規則
  TOP-REG は、行き先を最後の長い前置きのやり直しの着地の区域に、どのピンの原子よりも上に置いて成り立つ。（査読者：古い規則のパターンの点への条件が変わることを 1 文で書くこと。）
- **LAND-CAP**（移しで証明済み、FRAG のもと）。$`\min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ より下で $`G(\Omega_3+1) \le m_\lambda \lt G(\hat\zeta_\varepsilon)`$ のどのやり直し $`\lambda`$ でも $`r(\lambda) \lt H(\eta_\lambda + \Xi^*_\lambda + \omega^2)`$。
  ここで着地のずれ $`\Xi^*_\lambda`$ は、蓋のずれに最後の長い前置きのやり直しの着地の距離を足したもの（$`G(\hat\zeta_3)`$ より下では $`\Xi_\lambda`$ と同じ）。系：**$`G(\hat\zeta_\varepsilon)`$ より下のどの
  符号でも CAP-0**。EXACT-G($`\hat\zeta_3`$)：符号 $`G(\hat\zeta_3)`$ のやり直しは $`r(\lambda) = r(H(\eta_\lambda + G_2)) = \delta_L + 1`$、$`L = H(\eta_\lambda + G_2 + \omega^2)`$。LONG-CLASS$`^{19}`$（$`r(\lambda) \ge H(\eta_\lambda + \varepsilon_+)`$ なら
  $`m_\lambda \ge G(\hat\zeta_\varepsilon)`$）。LOW-RED$`^{19}`$：LOW$`_x`$ なら、$`x`$ より下に、符号が $`[G(\hat\zeta_\varepsilon), P')`$ にある自分を越える長いやり直しが共終に多くある。
- **DICHOTOMY-4′**（証明済み、FRAG のもと、仮定 $`H(\Omega_4 + G(\Omega_3) + Z + \omega^2) \le \nu_S`$ のもと）。$`u_4 = H(\Omega_4)`$ で：$`u_4`$ で CAP-0 が成り立つか、または $`u_4`$ より下で
  符号が $`[G(\hat\zeta_\varepsilon), G(\Omega_4))`$ のやり直しが共終に多く $`H(\eta + G(\Omega_3))`$ に届く。また $`r(u_4) \gt H(\Omega_4 + G_2 + \omega^2)`$。これは [SHIFT4-ja.md](SHIFT4-ja.md) §2.2 の二者択一（そこでは未証明）を直したもの。
  （査読者：2 つ目の場合の範囲は EXACT-LONG⁺ に立つ。それ無しでは範囲は $`[G(\hat\zeta_4), G(\Omega_4))`$。）
- **定理 X19**（証明済み、FRAG のもと）：

```math
\nu_C \ge X_{19} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_\varepsilon + \omega^{G(\hat\zeta_\varepsilon)+1}\cdot 2),\qquad G(\hat\zeta_\varepsilon) = \psi_{\Omega_2}(\Omega_\omega + \hat\zeta_\varepsilon).
```

だから **FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, X_{19}]`$ で両方の半分とも成り立つ**。$`\nu_S \ge X_{19}`$、$`X_{18} \lt H(\hat\zeta_3) \lt X_{19} \lt \psi_{\Omega_1}(\Omega_\omega + \Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$（Python と Lean で確かめた）。
また（P-LOW$`^{19}`$）$`H(\theta_2\cdot\omega^2) \lt a \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ で $`(a, b)`$ に (P) があるどのやり直し $`a`$ も $`m_a \ge G(\hat\zeta_\varepsilon)`$。EXACT-LONG⁺ 無しでは（この節のほかの補題は使って）同じ
証明が $`\nu_C \ge X_{19}^- = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_4 + \omega^{G(\hat\zeta_4)+1}\cdot 2)`$ を与える。**仮定つき。数えない**：LOW が偽なら $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\hat\zeta_\varepsilon)+1})`$。

- **未証明**（未解決）：$`\Omega_\omega`$ より下のどの正規の乗数でも着地の蓋（予想 READ$`^L`$。$`P'`$ より下のどの符号でも CAP-0 を与え、だから LOW を否定する。§2.1 で偽と分かった）。
  $`D \ge \varepsilon_+`$ での長いやり直しのちょうどの届く先（あらすじ：[SHIFT2-ja.md](SHIFT2-ja.md) §1.1 の基の取りかえを通る同じ証明で、符号 $`G(\Omega_1)`$ まで）。$`G(\Omega_1)`$ より先では実現の読み方と
  蓋の読み方が違い、一般の分離は知られていない。LOW。(P)。(Q′)。
- 査読者のほかの細かい点：代わりの道は違う確かめを引いている（要るのは $`[\hat\zeta_3, \hat\zeta_4)`$ のどの指数も $`G_2^2`$ より下であることで、査読者の試しがそれを示す）。ある出力が
  $`X_{19}`$ でない点に「X19」と名札を付けている。$`\hat\zeta_\varepsilon`$ での天井は査読者の試しを引くこと。EXACT-LONG⁺ の越えの補題の 1 つの場合（$`D = 0`$）は別に定義すること。

### 1.2 $`\nu_C = \nu_S`$：$`G_2^2`$ より下の TC⁺ と、$`\omega^{G_2^2}`$ より下のまたぎ

記号は [SHIFT3-ja.md](SHIFT3-ja.md) §1.4 と §2.4 と同じ（TC⁺、LOW、LOW$`^\omega`$、(D1b)、(E4)）。$`\pi_\eta = \psi_{\Omega_2}(\Omega_\omega + \theta\cdot\eta)`$。この小節の証明済みの結果はどれも段 1 でのもの。

- **D-UNC$`^\pi`$**（証明済み、FRAG 無し）。$`\eta \in D`$ と標準形 $`\xi \lt \pi_\eta`$ で：$`\eta + \xi \in D`$ ⟺ $`\xi`$ の定数が $`H(\eta + \xi)`$ より下。$`\eta`$ の項は吸い込まれてよい。
  （査読者：論文の言うのと違い、[SHIFT4-ja.md](SHIFT4-ja.md) §1.4 の D-UNC$`^Z`$ はこの場合ではない。$`\eta = 1, 2, \omega^2`$ ではずれ $`\xi = \pi_\eta \lt Z`$ が $`\eta + \xi \in D`$ を与え、D-UNC$`^\pi`$ はそれを含まない。）
- **BC$`^\pi`$**（段 1 で証明済み、FRAG 無し）。η の基の取りかえは、定数の無い上限 $`\Gamma \le \pi_\beta`$ より下のすべてのずれで定義され、行き先での吸い込みを許す。$`\nu_C = \nu_S`$ の
  設定ではどの基も $`H(\hat\zeta_2)`$ より上なので、$`\Gamma = G(\hat\zeta_2)`$ でよい。
- **READ-EQ**（証明済み）。基の取りかえは、$`G_2`$ より下の符号で読み方 $`\Theta`$ と入れ替えられる。これで [SHIFT3-ja.md](SHIFT3-ja.md) §1.4 の査読の細かい点が 1 つ片づく。
- **$`G_2^2`$ より下の TC⁺、MONO-F**（証明済み、FRAG のもと、段 1）。基の取りかえ $`B`$ は届く先を保つ（$`r(BR) = B(r(R))`$）：$`\tau \lt G_2`$ のどの短いやり直しでも、符号
  $`G_2\cdot D + m_0`$（$`D, m_0 \lt G_2`$）のどの長いやり直しでも、符号 $`G(\Omega_3)`$ でも。だから符号の移しはそのようなどの基の取りかえでも成り立つ。$`G_2^2`$ より下ではちょうどの届く先は符号について
  狭義増加。（査読者：どちらの半分にも FRAG が要る。論文の「≤ の半分は FRAG 無し」は間違い。）$`G_2^2`$ より先では上下からはさむ評価しか知られていない。
- **$`G(\hat\zeta_3)`$ より下の蓋をもう一度**（移しで証明済み、FRAG のもと）：§1.1 と同じ道で、$`G(\hat\zeta_3)`$ より下で CAP-0、$`\nu_C \ge X_{\hat\zeta_3} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_3 + \omega^{G(\hat\zeta_3)+1}\cdot 2)`$。これは $`X_{19}`$ より下の点。
  **未証明**：LOW が偽のときの対応する評価（段 2 でのこれらの蓋が要る）。（査読者：乗数が正規であることは欠かせない。正規でない $`\zeta \lt \hat\zeta_3`$ は $`R(\zeta) \ge G_2`$ になりうる。）
- **仮定つき。数えない**（LOW のもとで、FRAG のもとで正しい。論文は LOW$`^\omega`$ のもとで主張する）。η のずれが $`\omega^{G_2^2}`$ より下のどの (D1b) のまたぎでも：どの添字の不動点の先でも
  帳簿づけ、$`G(\hat\zeta_3)`$ より下での余地、$`G_2^2`$ より下の指数でのピンと遠い TOP-REG、記録したどのやり直しでも TC⁺（U0–U3）。だからこれらのまたぎは置ける（PLACE$`^{T2}`$、RES-ALL$`^{T2}`$）。
  $`c_u = H(\eta_u + \omega^{G_2^2})`$ は区域の系（ZONE$`^{(2)}`$）。**進行を止める点**：LOW$`^\omega`$ が足すのは $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ の場合だけで、予想した名前はこの場合を予言する。
  そこではこれらの段階に、長いやり直しのちょうどの届く先、CROSS-O とピン、$`G(\hat\zeta_3)`$ より下の蓋、LONG-CLASS、BC$`^\pi`$ の段 2 での形が要り、どれも証明されていない。だから
  [SHIFT3-ja.md](SHIFT3-ja.md) §1.4 の査読の進行を止める点（そこのすべてが LOW のもと）は残る。
- **残り**（論文の組み立て。LOW$`^\omega`$ を LOW に置き換え、あらすじの段階を 1 つ含む）。$`\nu_C = \nu_S`$ は次から出る：$`G_2^2`$ 以上の長い符号での、基の取りかえと入れ替えられるちょうどの
  届く先。$`G(\hat\zeta_3)`$ 以上の符号での蓋（余地）。TWIST のあとの点検（あらすじ）。LOW。§1.1 は $`D \lt \varepsilon_+`$ での長いやり直しのちょうどの届く先と $`G(\hat\zeta_\varepsilon)`$ より下の蓋を与えるが、それらが
  基の取りかえと入れ替えられることを示した論文は無い。$`\nu_C = \nu_S`$ も $`\nu_C \lt \nu_S`$ も **未解決**。
- 査読者のほかの細かい点：ピンでの引用 1 つ（READ-EQ ではなく区域の移し）。論文が使わないと言う辞書を 1 か所で使っている。最初の未解決の場合の符号は $`G_2^2`$ ではなく
  $`G_2^2 + 1`$。

### 1.3 どの η でも GEN、$`\psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$ までの素の符号

$`D_\infty`$ を $`\eta \in \mathrm{Cl}(\Omega_\omega + \theta\cdot\eta, H(\eta))`$ を満たすすべての順序数 $`\eta`$ の類、$`\iota(\eta)`$ を $`D_\infty \cap \eta`$ の順序型、$`\upsilon^\infty = \sup H[D_\infty]`$ と書く。

- **EXTRACT$`^\infty`$、NFD$`^\infty`$**（証明済み）。$`\eta \ge \Omega_\omega\cdot\omega`$ では項 $`\Omega_\omega`$ は $`\theta\cdot\eta`$ に吸い込まれるが、項 $`\omega^{\theta+a_i}`$ はやはりカントールの標準形の項なので、
  $`\eta`$ は前と同じに読み戻せる。吸い込まれた $`\Omega_\omega`$ は一度も使われていなかった。だから [SHIFT4-ja.md](SHIFT4-ja.md) §2.4 の障害（$`\Omega_\omega\cdot\omega`$ より先での GEN-EXT の取り出しの段階）は障害ではない。
- **定理 GEN-ALL**（証明済み。査読者は STEP と LOW-STEP の証明を 1 行ずつ読み直した：どちらも引数 $`A`$ に上限を置かない）。どの $`\eta \in D_\infty`$ でも：

```math
H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) = \upsilon_{1+\iota(\eta)}.
```

GEN、GEN-EXT、GEN⁺ は GEN-ALL を制限したものなので、[SHIFT4-ja.md](SHIFT4-ja.md) §2.4 のラベルの問題は片づく。$`I_\omega \in D_\infty`$ で $`\Omega_\omega + \theta\cdot I_\omega = I_\omega`$ なので、
核の読み方 A（[README-ja.md](README-ja.md) §2）の $`\psi_{\Omega_1}(I_\omega)`$ はそれ自身 $`\upsilon`$ 点で、$`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$。

- **基 $`\Omega_\omega\cdot\xi`$**（証明済み。基の道具は移しで、η の形の道具は目録の水準の移しで）。$`\Omega_\omega\cdot\xi \in D_\infty`$ のどの $`\xi \ge 1`$ でも、点 $`\psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$ は
  符号 $`P_\xi = \psi_{\Omega_2}(\Omega_\omega\cdot(1+\xi))`$ のやり直し。$`\pi_\eta`$ より下のずれで D-UNC。基の取りかえ、不動点、辞書、分け方、符号の移しは段 $`1+\xi`$ で成り立つ。
- **PUSH$`^{\omega^\omega}`$**（証明済み。鎖の長さ 3。導き方は **査読 2 回**：[SHIFT4-ja.md](SHIFT4-ja.md) §2.4 の仮定つきの結果で、今はその仮定を GEN-ALL が満たす）。素の符号で

```math
\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega).
```

狭義の $`\gt`$ には、[SHIFT3-ja.md](SHIFT3-ja.md) §1.2 の証明されていない注意が要る。

- **名前の半分**（証明済み）。$`\upsilon^\infty`$ より下のどの $`\upsilon`$ 点も（だからそこのどのやり直し、ブロックの始まり、添字の不動点も）ちょうどの名前 $`H(\eta)`$（$`\eta \in D_\infty`$）を持つ。
  $`\psi_{\Omega_1}(I_\omega)`$ より下ではそのつぶす関数の引数は $`I_\omega`$ より下。**REL-ETA**（移しで証明済み）は $`\upsilon^\infty`$ より下のどの長いやり直しでも成り立つ。（査読者：論文の見出しは
  LOW$`^\omega`$ はもう要らないと言うが、それは未解決の $`\nu_C \lt \upsilon^\infty`$ に置き換わっただけ。）
- **定理 X$`^{(1+\xi)}`$**（証明済み、FRAG のもと。$`\Omega_\omega\cdot\xi \in D_\infty`$ のどの $`\xi \ge 1`$ でも）：$`\nu_C`$ は $`(\psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi)), Y_\xi)`$ に無い。$`Y_\xi = \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi) + \omega^{\mathbb{G}^\vartheta+1})`$
  （$`\mathbb{G}^\vartheta`$ は [SHIFT3-ja.md](SHIFT3-ja.md) §1.1 のもの。FRAG 無しでは $`\mathbb{G}^\vartheta`$ の代わりに $`G_2`$）。$`\xi = 1`$ が [SHIFT3-ja.md](SHIFT3-ja.md) §2.4 の X$`^{(2)}`$。**仮定つき。数えない**：
  $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$ なら $`R_2^C`$ で主張は $`[0, Y_\xi]`$ で成り立つ。$`\xi \lt I_\omega`$ で証明済み。$`\xi \ge I_\omega`$ では**未証明**（進行を止める点。論文はどの $`\xi`$ でも
  主張した）：$`\psi_{\Omega_1}(I_\omega)`$ の標準形は引数 $`I_\omega`$ のものしか無いので、$`[0, Y_\xi]`$ は読み方 A に収まらず、そこで $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$ なら読み方 A は否定される。
- **未解決**：LOW、CAP-0、CAP-1 と、段 $`1+\xi`$ でのそれらの類似。段 $`\ge 2`$ での $`\tau \ge \Omega_2`$ のやり直しの届く先。(P)。素の符号では：$`\Theta_1`$ より先の $`\mathrm{CH}_2`$（変わらず）。
  $`\omega^\omega`$ 以上の段階（鎖の数 4 が要るので $`\iota(\mathrm{CH}_4)`$ の評価になる）と非可算の段階の添字。$`\psi_{\Omega_1}(\Omega_\omega\cdot T)`$ の形の素の評価を、順序数の側はもう制限しない。
- 査読者のほかの細かい点：$`\theta\cdot\Omega_1 = \Omega_1`$ は偽（害は無い。[SHIFT4-ja.md](SHIFT4-ja.md) §2.4 の論文にも同じ書き違いがある）。定数の集合の 1 つが $`\{1\}`$ を落としている（害は無い）。
  論文は可算の段や $`[P_\xi, \pi_\eta)`$ のずれを試していない（査読者が試した）。1 つの段階は帰納法ではなく、下の段での η の形の道具の適用。

### 1.4 25 回目のあとの状態

26 回目から 37 回目でこの状態は変わった。§2.4 と [SHIFT6-ja.md](SHIFT6-ja.md) §3.4、[SHIFT7-ja.md](SHIFT7-ja.md) §1.4、§2.4、§3.4、[SHIFT8-ja.md](SHIFT8-ja.md) §1.4、§2.4、[SHIFT9-ja.md](SHIFT9-ja.md) §1.4、§2.4、§3.4 を見よ。

- $`R_2^C`$ での Wilken の主張：$`[0, X_4]`$ では FRAG 無しで、$`[0, X_{19}]`$ では FRAG のもとで（$`[0, X_{18}]`$ は査読 2 回）両方の半分とも成り立つ。核の側は $`[0, \nu_C]`$ で成り立つ。
  $`\nu_C`$ の InaccPsi による上からの評価は無い：名前の付いた組での (P) は未解決のまま。
- 届く先：$`\tau \lt G_2`$ のどの短いやり直しと $`D \lt \varepsilon_+`$ のどの長いやり直しでもちょうど分かる（FRAG のもと）。$`G(\hat\zeta_\varepsilon)`$ より下のどの符号でも蓋。
- 名前：$`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ より下のどの $`\upsilon`$ 点も名前 $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ を持つ。
- $`\theta_0`$ より下の下からの評価のための計画：SRO より下の段は、標本の 3,166 個すべてですべての $`n`$ で成り立つ（変わらず）。素の符号で $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$、
  $`\iota(\mathrm{CH}_2) \ge \Theta_1`$。
- 上からの評価：$`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ の InaccPsi の項による評価はまだ無い。
- $`\nu_C = \nu_S`$：LOW は決まっていない。CAP-0 は $`G(\hat\zeta_\varepsilon)`$ より下のどの符号でも成り立つ（FRAG のもと）。TC⁺ は段 1 で $`G_2^2`$ より下で成り立つ。残り：(P1)、(D1b)、(E4)。

### 1.5 25 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。名前、標準形、読み方、順の鎖 $`X_{17} \lt X_{18} \lt \dots \lt X_{19}^- \lt X_{19} \lt H(\Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ を Python と Lean で（緑）。正規の乗数 3,000 個の指数、
  余白、組 861,202 個での順、着地のずれ 2,400 個での D-UNC、天井、最小の倍数の補題：失敗 0。査読者：細かい蓋への反例。標本 611 個での $`\hat\zeta_\varepsilon`$ での天井。
  $`\hat\zeta_4`$ と $`\hat\zeta_\varepsilon`$ の近くの指数（組 30,338 個）。ずれ 1,572 個での D-UNC。組 198,787 個での余白：失敗 0。Lean の再実行と自前の Lean のファイルは緑。
- §1.2。層の上限、$`R(\hat\zeta_3) = G_2`$、乗数 1,039 個、ずれ 4,423 個（吸い込みのあるもの 1,532 個）での D-UNC$`^\pi`$、符号 388 個での原子の置き換え：失敗 0（Python だけ）。査読者：正規の
  乗数 238 個、段 3 の基でずれ 1,219 個での D-UNC$`^\pi`$：失敗 0。順の鎖の Lean のファイルは緑。
- §1.3。$`\Omega_\omega\cdot\omega`$ から $`I_\omega + \theta`$ までの 15 個の引数 $`A`$ での STEP の写像 $`B`$ と LOW-STEP の写像 $`E`$（組およそ 600 万個）、9 つの段の値 1,620 個での標準形の試し、2,016 回の試しでの
  D-UNC、標本 429 個での符号：失敗 0。$`E`$ の壊した変種 3 つは失敗する。Lean は緑。査読者：ほかの包での取り出し（8,012 回の試し）、$`H`$ と $`\pi`$ の狭義増加（組 25,440 個）、
  $`[P_\xi, \pi_\eta)`$ のずれでの D-UNC（792 回の試し）、$`A`$ に可算の原子を持つ $`B`$ と $`E`$（組およそ 600,000 個）：失敗 0。Lean の再実行は同じ。

### 1.6 未解決

26 回目から 37 回目でこの一覧は変わった。今の一覧は [SHIFT9-ja.md](SHIFT9-ja.md) §3.6 にある。

- 上からの評価：$`\nu_C`$ について名前の付いた 1 つの組での (P) と (Q′)。(P) には $`G(\hat\zeta_\varepsilon)`$ より先の蓋と、符号 $`P'`$ での下からの評価が要り、(Q′) には $`L(\omega)`$ の等最小の
  パターンが要る。$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価。
- FRAG のもとで $`X_{19}`$ より上の主張：$`D \ge \varepsilon_+`$ での長いやり直しのちょうどの届く先（$`G(\Omega_1)`$ まではあらすじ）。$`G(\Omega_1)`$ より先での分離。どの $`\Omega_k`$ でも着地の蓋（READ$`^L`$。今は偽、§2.1）。
  $`\Omega_3`$ より上の層の下からの評価の側。
- 最初の到達不能基数：$`\omega^\omega`$ 以上の素の段階、非可算の段階の添字、$`\Omega_{\omega+1}`$。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準形の行列での段。
- $`\nu_C = \nu_S`$：LOW（符号が $`[G(\hat\zeta_\varepsilon), P')`$ での CAP-0）、LOW$`^\omega`$（今は：§1.2 の道具の段 2 での形）、$`G_2^2`$ 以上の長い符号での TC⁺、置くための $`G(\hat\zeta_3)`$ 以上の
  符号での蓋、(D1b)、(E4)。
- 名前：$`R(\Theta_{d\omega})`$；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ；届く先を符号で書く InaccPsi の式；$`X_{19}`$ より先の名前；
  [COVER-ja.md](COVER-ja.md) §9 の残り。

## 2. 26 回目

3 つの論文（2026-10）。どれも 1 回ずつ査読された。だからこの節の結果は、回数を書いていなければ査読 1 回。**査読 2 回** とは、25 回目の査読者が
直しを出した（またはその結果を確かめた）うえで、この回の査読者が書き出したものをもう一度確かめたもの。どの論文も Wilken, JSL 72 (2007)、
Carlson, AML 38 (1999)、Wilken, AML 45 (2006)、Carlson 2009, p. 97 が予告する同値を使わない。引く論文：§2.1 で [W07b]（L.2.1、Thm 2.2、Thm 5.3 の証明）。
§2.2 と §2.3 の証明済みの段階はどの論文も使わない（§2.3 は注意の中で Carlson 2001 を引くだけで、FRAG も使わない）。Lean のファイルは足していない：
どの論文も項を比べるだけの Lean のファイルを確かめた（`#eval`、定理は無い。緑で、査読者の再実行でも緑）。これらは確かめた扱い。
25 回目の査読の細かい点は反映した：§1.1 へのものは §2.1 の論文が、§1.2 へのものは §2.2 の論文が反映し、その査読者がもう一度確かめた（**査読 2 回**。
ただし 1 行を除く。§2.2 を見よ）。残りは §1 に書いた。段の番号は [SHIFT-ja.md](SHIFT-ja.md) と同じ（論文より 1 つ大きい）：段 1 は $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ より下で、
段 $`1+\xi`$ はやり直し $`H(\Omega_\omega\cdot\xi + \eta')`$（$`0 \lt \eta' \lt \Omega_\omega`$）からなる。

§1 と [SHIFT2-ja.md](SHIFT2-ja.md) §1、§2.1 の名前：$`\Phi' = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\omega^2 + \Omega_2)`$、$`\hat G = G(\Omega_2)`$（$`G`$ の最小の不動点）、やり直し $`\lambda`$ について
$`F_\lambda = H(\eta_\lambda + \Omega_1)`$（その最初の添字の不動点）。この回の新しい名前（乗数には $`\hat\zeta_3`$ と同じく ^ を付ける）：

```math
\hat g_3 = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot\Omega_3),\quad \hat\zeta_G = \theta_3\cdot\Omega_3,\quad \hat\zeta_A = \hat\zeta_G + \Omega_2,\quad \hat\zeta_H = \hat\zeta_G + \omega^{\hat g_3+g_3},\quad \hat\zeta_f = \hat\zeta_H + \Omega_2.
```

$`R(\hat\zeta_G) = \hat G`$、$`R(\hat\zeta_A) = \hat G + \Omega_1`$、$`R(\hat\zeta_H) = \omega^{\hat G+G_2}`$、$`R(\hat\zeta_f) = \omega^{\hat G+G_2} + \Omega_1`$、$`\hat\zeta_\varepsilon \lt \hat\zeta_G \lt \hat\zeta_A \lt \hat\zeta_H \lt \hat\zeta_f \lt \Omega_4`$（確かめた）。

### 2.1 最初の添字の不動点までの長いちょうどの届く先。READ$`^L`$ は偽。包の蓋：FRAG のもとで $`\nu_C \ge X_{21}`$

- **§1.1 への査読の細かい点を反映した**（証明済み、**査読 2 回**）。$`G(\hat\zeta_3)`$ より下で証明した蓋を今は粗い蓋と呼び、NO-LIT は粗い蓋についての主張だけ
  （ブロックの番号を $`\ge 2`$ の最小にとる細かい形は $`\hat\zeta_3`$ より下の $`\theta_3\cdot(\omega\cdot 2+1)`$ で偽）。$`\hat\zeta_\varepsilon`$ での天井は読み方の 1 行の議論で証明し、試しは
  その裏づけ。EXACT-LONG⁺ の越えの補題の場合 $`D = 0`$ は、EXACT-CL\* が与える値として定義した。§1.1 の代わりの道は「EXACT-LONG⁺ 無し」で、正しい試しを引く。
  DICHOTOMY-4′ の範囲は EXACT-LONG⁺ のあるときと無いときの両方で書いた。
- **THETA$`^V`$、EXACT-LONG$`^V`$**（THETA$`^V`$ は証明済み。EXACT-LONG$`^V`$ は移しで証明済み、FRAG のもと）。$`G_2`$ の上のヴェブレンと Γ の層で、読み方 $`\Theta^V`$ は
  $`\Phi'`$ より下の符号を始めの区間の上へ写し、移しと入れ替えられる。だから符号 $`G_2\cdot D + m_0`$（$`D \lt \Phi'`$）の長いやり直しの届く先はちょうど分かる。
- **THETA$`^G`$**（証明済み）。数える規則 PSI-θ（[SHIFT3-ja.md](SHIFT3-ja.md) §2.1）は $`\hat G`$ より下のどの乗数でも成り立つ。これで素の順序型の読み方 $`\Theta_\lambda`$ を $`\hat G`$ より下の
  すべての符号で定義する：$`[G(\zeta), G(\zeta+1))`$ の符号は、動いた基 $`\upsilon_{\lambda+1+\Theta_\lambda(\zeta)}`$ で読む。これはそれらの符号を $`[0, F_\lambda)`$ の上へ写し、移しと入れ替えられる。
  [SHIFT2-ja.md](SHIFT2-ja.md) §2.1 の実現の読み方と蓋の読み方（$`G(\Omega_1)`$ より先で違う）は、これの下と上にある。（査読者：段階の 1 つ「上限は $`F_\lambda`$ 以下」の議論は
  間違い。査読者が出す帰納法で成り立つ。引用を 2 つ足すこと：非可算の乗数での形には高い部分つきの PSI-n が要り、符号の覆いの補題も要る。読み方が包の中に
  留まることを書くこと。27 回目に反映した、[SHIFT6-ja.md](SHIFT6-ja.md) §1.1。）
- **EXACT-LONG$`^G`$、EXACT-F**（移しで証明済み、FRAG のもと）。符号 $`G_2\cdot D + m_0`$（$`m_0 \lt G_2`$）の長いやり直し $`\lambda`$ の届く先は、どの $`D \lt \hat G`$ でもちょうど分かる：
  添字の距離 $`\omega^2\cdot\Theta_\lambda(D)`$ に着地し、それは $`F_\lambda`$ より下。$`D = \hat G`$ では $`F_\lambda`$ そのものに着地する：やり直し $`F = H(\eta_\lambda + \Omega_1)`$ について
  $`r(\lambda) = r(F) + \Theta_F(m_0)`$（$`m_0 \lt \theta`$ のとき）。だから長いちょうどの届く先は今は最初の添字の不動点に届く。前は $`D \lt \varepsilon_+`$ で分かっていた。（査読者：行き先には
  §1.1 の規則 TOP-REG-LAND を引くこと。遠い規則 TOP-REG-FAR は $`\delta_j\cdot\omega`$ より下の行き先しか含まない。）
- **$`\hat\zeta_\varepsilon`$ より先の LAND-CAP**（移しで証明済み、FRAG のもと）。§1.1 の着地の蓋は $`[G(\Omega_3+1), G(\hat\zeta_A))`$ のどの符号でも成り立つ。族 $`\hat G`$（$`[G(\hat\zeta_G), G(\hat\zeta_A))`$
  の符号）も含む。鋭い越え CROSS-SHARP$`^{(3)\prime\prime}`$ は $`\hat\zeta_G`$ まで成り立つ。EXACT-G($`\hat\zeta_G`$)：符号 $`G(\hat\zeta_G)`$ のやり直しは、やり直し $`H(\eta_\lambda + \hat G + \Omega_1)`$ と
  ちょうど同じところまで届く。
- **NO-READL**（移しで証明済み、FRAG のもと。新しい EXACT-LONG$`^G`$ と EXACT-F に立つ）。§1.1 の予想 READ$`^L`$（どの正規の乗数でも着地の蓋）は **偽**。
  $`G(\hat\zeta_A)`$ より下のどの符号でも成り立つが、符号
  $`G(\hat\zeta_A) = \psi_{\Omega_2}(\Omega_\omega + \theta_3\cdot\Omega_3 + \theta_2\cdot\Omega_2)`$ のどのやり直しでも成り立たない。反例：$`\lambda = H(\theta_2\cdot\hat\zeta_A) = \psi_{\Omega_1}(\Omega_\omega + \theta_3\cdot\Omega_3 + \theta_2\cdot\Omega_2)`$。READ$`^L`$ は
  $`r(\lambda) \lt H(\eta_\lambda + \hat G + \Omega_1 + \omega^2)`$ と言うが、$`r(\lambda) \ge H(\eta_\lambda + \hat G + \Omega_1 + \omega^2)`$。使う点は $`X_{20} \le \nu_S`$（下）より下にあるので、仮定を足す必要は無い。
  原因：族 $`\hat G`$ の符号は添字の不動点に着地し、そこから可算の分だけ進んで、次の族が始まる点を越える。（査読者：蓋の値が「着地の最大」という注意の読み方に
  よらないことを書くこと。）
- **$`G(\hat\zeta_H)`$ より下の CAP$`^\sharp`$、READ$`^\sharp`$**（移しで証明済み、FRAG のもと）。包の蓋：読み方が $`X + \Omega_1`$ で、$`X`$ の最後が商 $`\hat G`$ の長い符号である族では、
  蓋のずれを $`F'' = H(\eta_\lambda + X + \Omega_1)`$ だけずらす。このずらしで、蓋は $`[G(\Omega_3+1), G(\hat\zeta_H))`$ のどの符号でも成り立つ。系：**$`G(\hat\zeta_H)`$ より下のどの符号でも
  CAP-0**。LONG-CLASS$`^{21}`$（$`r(\lambda) \ge H(\eta_\lambda + \omega^{\hat G+G_2})`$ なら $`m_\lambda \ge G(\hat\zeta_H)`$）。LOW-RED$`^{21}`$：LOW$`_x`$ なら、$`x`$ より下に、符号が $`[G(\hat\zeta_H), P')`$ にある
  自分を越える長いやり直しが共終に多くある。$`G(\hat\zeta_A)`$ では届く先は $`[H(\eta + \hat G + \Omega_1 + \omega^2), H(\eta + \hat G + \Omega_1 + F'' + \omega^2))`$ にある。ちょうどの値は未解決。
- **DICHOTOMY-4″**（証明済み、FRAG のもと、DICHOTOMY-4′ の仮定のもと）。$`u_4 = H(\Omega_4)`$ で CAP-0 が成り立つか、または $`u_4`$ より下で符号が
  $`[G(\hat\zeta_H), G(\Omega_4))`$ のやり直しが共終に多く $`H(\eta + G(\Omega_3))`$ に届く。だから台の頂上の符号 $`G(\Omega_4)`$ そのものでの READ$`^L`$ は否定されていない。NO-READL が否定するのは一般の形。
- **定理 X21**（証明済み、FRAG のもと）：

```math
\nu_C \ge X_{21} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_H + \omega^{G(\hat\zeta_H)+1}\cdot 2),\qquad G(\hat\zeta_H) = \psi_{\Omega_2}(\Omega_\omega + \hat\zeta_H).
```

だから **FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, X_{21}]`$ で両方の半分とも成り立つ**。$`\nu_S \ge X_{21}`$、$`X_{19} \lt X_{20} \lt X_{21} \lt H(\Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$（Python と Lean で確かめた）。
また（P-LOW$`^{21}`$）$`H(\theta_2\cdot\omega^2) \lt a \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ で $`(a, b)`$ に (P) があるどのやり直し $`a`$ も $`m_a \ge G(\hat\zeta_H)`$。CAP$`^\sharp`$ 無しでは同じ証明が
$`\nu_C \ge X_{20} = \psi_{\Omega_1}(\Omega_\omega + \theta_2\cdot\hat\zeta_A + \omega^{G(\hat\zeta_A)+1}\cdot 2)`$ を与え、新しい道具の一部だけでは $`X_{19}`$ と $`X_{20}`$ の間の 3 つの点を与える。（査読者：$`\hat\zeta_A`$ での
天井は確かめただけでなく証明済み。）**仮定つき。数えない**：LOW が偽なら $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{G(\hat\zeta_H)+1})`$。

- **未証明**（未解決。$`\theta_2+1`$ での PSI-θ による $`D \lt G(\hat\zeta_3)`$ の長いちょうどの届く先、[SHIFT6-ja.md](SHIFT6-ja.md) §1.1、はいくつかの符号で進行を止める点を持っていた、そこの §2.1。そこの §3.1 の直した値で証明済みで、$`\varepsilon_{G(\hat\zeta_G)+1}`$ までも同じ）：$`D \gt \hat G`$ での長いちょうどの届く先（$`\Phi^{\hat G}`$（$`\hat G`$ の上の $`\Phi'`$ の類似）より下では基 $`F_\lambda`$ で読むあらすじ。$`\Phi^{\hat G}`$ からは添字
  $`\theta_2 + 1`$ での PSI-θ が要り、それは証明されていない。実現の読み方と蓋の読み方がまだ違うのはここ）。$`\hat\zeta_H`$ より先の READ$`^\sharp`$（予想。やり直し自身の前置きによる
  最初の越えは $`\hat\zeta_f`$。$`\Omega_k`$（$`k \ge 4`$）と $`\Omega_\omega`$ では包が入れ子になる）。どの正規の乗数でも READ$`^\sharp`$ なら $`P'`$ より下で CAP-0、だから LOW は偽。LOW。(P)。(Q′)。
- 査読者のほかの細かい点：NO-READL は新しい EXACT-LONG$`^G`$ と EXACT-F に頼る（NO-LIT は頼らなかった）。途中の長いやり直しの蓋について 1 行（移しの定義域に入る）。
  実現の写像の定義域について足りない 1 行。移しの補題の上限より上のずれについての注意（前の査読者が認めた使い方）。（どれも 27 回目に反映した、[SHIFT6-ja.md](SHIFT6-ja.md) §1.1。）

### 2.2 $`\nu_C = \nu_S`$：どの段でも道具、どの段でも TC⁺

記号は §1.2 と同じ。$`m^*_\xi = \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi))`$（段 $`1+\xi`$ の始まり）。LOW$`^\infty`$：$`\nu_C \lt \upsilon^\infty`$（§1.3）。LOW$`^\omega`$ からこれが出る。

- **§1.2 への査読の細かい点を反映した**（証明済み、**査読 2 回**）：TC⁺ のどちらの半分にも FRAG が要る。D-UNC$`^Z`$ は段 1 では D-UNC$`^\pi`$ の場合ではない（上の段では
  場合になる）。辞書のどの部分を使うか。**未証明**：書き直した長い前置きのピン（区域の移しの引用と、像についての 2 つの場合）は、符号の原子が動く区域にある場合に
  成り立たない（進行を止める点。下）。
- **TAIL-LEVEL、OFF-INF$`^{\mathrm{lev}}`$、REAL$`^{\mathrm{lev}}`$、CEIL$`^{\mathrm{lev}}`$**（証明済み）。終わりの区間での帰納法はやり直しの段から出ない。ずれの補題、$`\pi_\eta`$ より下のどの符号の
  実現、天井はどの段でも成り立つ。前の証明では「$`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ より下」という上限はどれも $`\eta`$ を $`D`$ に入れるためだけに使われていて、論文はその場所と置き換えを
  1 つずつ挙げる。（ついでの直し：[SHIFT4-ja.md](SHIFT4-ja.md) §2.1 の、EXACT-CL\* の尾はその区間に留まるという規則には、証明が選ぶとおり尾の始まりを $`H(z_0)`$ より上にとることが
  要る。今の書き方のままでは $`\nu = H(\omega^\omega + \omega^2)`$ が反例。）
- **どの段でも道具**（移しで証明済み。もとの証明が FRAG を使うところは FRAG のもと）。EXACT-C、EXACT-CL\*、GAP$`_j`$、蓋 R-CAP\*、LONG-CLASS、ピン（FAR-PIN、MULTI-RC\*、
  PIN-IDX、PIN-ALL、TOP-REG-FAR）、$`D \lt G_2`$ での EXACT-LONG と CROSS-O、EXACT-LONG-CL\*、EXACT-G($`\Omega_3`$)、θ と θ⁺ の層、$`\hat\zeta_2`$ と $`\hat\zeta_3`$ より下の READ、SEP$`^{G_2}`$、
  $`G(\hat\zeta_3)`$ より下の CAP-0、BC$`^\pi`$（違う段のやり直しの間でも）と READ-EQ は、$`\min(\nu_S, \upsilon^\infty)`$ より下のやり直しについて、どの段 $`\ge 1`$ でも成り立つ。（査読者：θ の層の
  蓋は辞書と査読済みの目録の水準でだけ証明されている。照合の表にその行を足すこと。）
- **どの段でも TC⁺、MONO-F**（証明済み、FRAG のもと）。どの段のやり直しの間の BC$`^\pi`$ の基の取りかえ $`B`$ でも（吸い込みを許す）：$`\tau \lt G_2`$ のどの短いやり直しでも、
  符号 $`G_2\cdot D + m_0`$（$`D, m_0 \lt G_2`$）のどの長いやり直しでも、符号 $`G(\Omega_3)`$ でも $`r(BR) = B(r(R))`$。段 1 ではこれは §1.2 の TC⁺ で、今は **査読 2 回**。段 2 では新しい。
- **定理 X$`^{(1+\xi)}`$ の改良**（証明済み、FRAG のもと。どの $`\xi \ge 1`$ でも）：$`\nu_C`$ は $`(m^*_\xi, Y'_\xi)`$ に無い。$`Y'_\xi = \psi_{\Omega_1}(\Omega_\omega\cdot(1+\xi) + \omega^{G(\hat\zeta_3)+1}) \gt Y_\xi`$（§1.3）。
  **仮定つき。数えない**：$`\nu_C \gt m^*_\xi`$ かつ $`\xi \lt I_\omega`$ なら、$`R_2^C`$ で主張は $`[0, Y'_\xi]`$ で成り立つ。LOW が偽なら $`\nu_C \ge Y'_1`$。
- **仮定つき。数えない**（LOW$`^\infty`$ のもとで、FRAG のもとで正しい）：η のずれが $`\omega^{G_2^2}`$ より下の (D1b) のまたぎについての、§1.2 の帳簿づけ、余地、区域の系。
  **進行を止める点**：符号が動く区域に原子を持つ長い前置きのピンには、動く下の原子についての PIN-ALL の形が要り、それは書かれていない（査読者は直せると見ている。27 回目に直した、[SHIFT6-ja.md](SHIFT6-ja.md) §1.2）。
  それまでは、ピン、遠い TOP-REG、置き方 PLACE$`^{T2}`$、RES-ALL$`^{T2}`$、下の残りは、長い前置きの符号がそのような原子を持たないまたぎでだけ成り立つ。
  だから §1.2 の進行を止める点は動く：段 2 の道具は今は証明済みで、足りないのはこのピンと LOW$`^\infty`$。
- **残り**（進行を止める点を直したあとの論文の組み立て）。$`\nu_C = \nu_S`$ は次から出る：$`[G_2^2, \Omega_2)`$ の符号での、基の取りかえと入れ替えられるちょうどの届く先。
  $`G(\hat\zeta_3)`$ 以上の符号での蓋（余地）。TWIST のあとの点検（あらすじ）。LOW$`^\infty`$（未解決）。$`\nu_C = \nu_S`$ も $`\nu_C \lt \nu_S`$ も **未解決**。
- 査読者のほかの細かい点：論文は TC⁺ についての前の進行を止める点が取り除かれたと言うが、道は今は LOW$`^\infty`$ に立つので言い過ぎ。段をまたぐ基の取りかえの
  1 つの場合（$`a' = m^*_\xi`$）が抜けているが成り立つ。符号 0 はやり直しを与えない。（27 回目に反映した、[SHIFT6-ja.md](SHIFT6-ja.md) §1.2。）

### 2.3 素の符号：段階の区域としての飾り、$`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$

言葉は [SHIFT3-ja.md](SHIFT3-ja.md) §1.2、§1.3 と同じ：段階、組のブロック、鎖の数。**飾り** とは、ある $`v \gt e`$ で $`e \le_1 v`$ となり、組に入らない元 $`e`$ のこと。

- **SUPPLY-0**（証明済み）。$`v \gt e`$ で $`e \le_1 v`$ なら、どの $`\xi \lt e`$ についても、$`e`$ の加法的主要数の写しが $`(\xi, e)`$ にある（$`e`$ で集合 $`\{e\}`$ について Carlson の規則 R1）。
  だから飾りは、組の根と同じく自由な段を出すが、組ではなく、鎖に輪を足さない。§1.3 が $`\omega^\omega`$ 以上の段階に要ると言った 2 つ目の組（鎖の数 4）は要らない。
- **区域**（証明済み：WT、DEC-SUP、DEC-REGION）。どの段階 $`1 \le T \lt \varepsilon_0`$ にも、入れ子の飾りからなり、それぞれのあとに自由な運び手が続く、組の無い区域の符号がある。
  飾りは自分より下に、より低いどの種類の単位も出す（DEC-SUP）。$`T' \lt T`$ なら $`T'`$ の区域は $`T`$ の区域の中に実現される（DEC-REGION）。$`\omega^\omega`$ より下ではこれらは組のブロックの
  自由な段。（査読者は自前のコードで組 $`T' \lt T`$ 42,901 個で作り方を走らせ、誤り 0。壊した版 2 つは捕まる。）
- **区域を使う素の側**（証明済み）。組のブロックの形、頂上、行の補題と、宿の補題は、自由な段の代わりに区域を使って成り立つ。パターンは扇を持たず、鎖の数は 2 以下。
- **$`T \lt \varepsilon_0`$ での順序数の側**（移しで証明済み）。$`\Omega_\omega`$ を基とする $`\psi`$ の数える規則と §1.3 の引数の補題は、$`\varepsilon_0`$ より下のどの段階でも成り立つ。$`T`$ による入力は
  2 つだけで、どちらも $`\varepsilon_0`$ より下で成り立つ。（査読者：$`T`$ による入力の一覧は足りないが、抜けたものはどれもどの $`T`$ でも成り立つ。）
- **PUSH$`^{\varepsilon_0}`$**（証明済み。鎖の長さ 3）。素の符号で、どの $`1 \le S \lt \varepsilon_0`$ でも $`\iota(\mathrm{CH}_3) \gt \psi_{\Omega_1}(\Omega_\omega\cdot(1+S))`$。だから

```math
\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0),
```

また、どの $`T \lt \varepsilon_0`$ でも $`\iota(\mathrm{CH}_4) \gt \psi_{\Omega_1}(\Omega_\omega\cdot T)`$。前は $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$。だから RED-TOWER は素の符号で $`\psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$ より下のどの $`t`$ も含む。
- **仮定つき。数えない**（今は証明済み、[SHIFT6-ja.md](SHIFT6-ja.md) §1.3）：$`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ は $`T \mapsto \psi_{\Omega_1}(\Omega_\omega\cdot T)`$ の最小の不動点（確かめた。証明はあらすじ）。STAGE-TOWER（あらすじ）：下の符号の系を
  まるごと段階の札の符号に使う。$`\varepsilon_0`$ 以上の可算の札についての順序数の側（あらすじ）と合わせれば $`\sup_k \iota(\mathrm{CH}_k) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ を与える。
  （査読者：あらすじの中に穴が 2 つある。$`Z_\omega`$ より下に 1 つの系は無いので、各 $`Z_n`$ より下の系を 1 つずつ使うこと。写した札には運び手が要り、基より上にあることを示すこと。どちらも 27 回目に行った、[SHIFT6-ja.md](SHIFT6-ja.md) §1.3。）
- **未解決**：$`\varepsilon_0`$ より先の、鎖の数 2 の組の無い区域の符号。$`\xi \ge \Omega_1`$ の札 $`\Omega_\omega\cdot\xi`$（その符号は引数を持ち、段階の系はそれを除く）。$`\Omega_\omega`$ 以上の札。
  $`\theta_0`$ ははるか上：$`\psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0) \lt \psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1) \lt \psi_{\Omega_1}(\Omega_{\omega+1}) \lt \psi_{\Omega_1}(\Omega_{\Omega_\omega}) \lt \theta_0`$（Python と Lean で確かめた）。
- 査読者のほかの細かい点：補題の 1 つの部分は要らない。古い元と新しい元を合わせたものが閉じていることを書くこと。2 つ目の組は「偽」より「要らない」が正確。
  1 つの比較は HOST$`_4`$ を引くこと。1 つの標本には証明書が無い（手で確かめた。証明済みのものはこれに頼らない）。Carlson 2001（pp. 19–20）は、論文が引く同一視を予告するだけ。（27 回目に反映した、[SHIFT6-ja.md](SHIFT6-ja.md) §1.3。）

### 2.4 26 回目のあとの状態

27 回目から 37 回目でこの状態は変わった。[SHIFT6-ja.md](SHIFT6-ja.md) §3.4、[SHIFT7-ja.md](SHIFT7-ja.md) §1.4、§2.4、§3.4、[SHIFT8-ja.md](SHIFT8-ja.md) §1.4、§2.4、[SHIFT9-ja.md](SHIFT9-ja.md) §1.4、§2.4、§3.4 を見よ。

- $`R_2^C`$ での Wilken の主張：$`[0, X_4]`$ では FRAG 無しで、$`[0, X_{21}]`$ では FRAG のもとで（$`[0, X_{18}]`$ は査読 2 回）両方の半分とも成り立つ。核の側は $`[0, \nu_C]`$ で成り立つ。
  $`\nu_C`$ の InaccPsi による上からの評価は無い：名前の付いた組での (P) は未解決のまま。
- 届く先：$`\tau \lt G_2`$ のどの短いやり直しと $`D \le \hat G`$ のどの長いやり直しでもちょうど分かる（FRAG のもと）。$`G(\hat\zeta_H)`$ より下のどの符号でも包の形の蓋。着地の蓋 READ$`^L`$ は偽。
- 名前：変わらず（$`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ より下のどの $`\upsilon`$ 点も名前 $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ を持つ）。
- $`\theta_0`$ より下の下からの評価のための計画：SRO より下の段は、標本の 3,166 個すべてですべての $`n`$ で成り立つ（変わらず）。素の符号で $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$、
  $`\iota(\mathrm{CH}_2) \ge \Theta_1`$。
- 上からの評価：$`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ の InaccPsi の項による評価はまだ無い。
- $`\nu_C = \nu_S`$：LOW は決まっていない。CAP-0 は $`G(\hat\zeta_H)`$ より下のどの符号でも成り立つ（FRAG のもと）。道具と $`G_2^2`$ より下の TC⁺ はどの段でも成り立つ。残り：動く原子のある
  ピン、LOW$`^\infty`$、(D1b)、(E4)。

### 2.5 26 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §2.1。名前、標準形、読み方、順の鎖 $`X_{19} \lt X_{20} \lt X_{21} \lt H(\Omega_4)`$ を Python と Lean で（緑、同じ出力）。$`[\hat\zeta_3, \Omega_4)`$ の正規の乗数 899 個の指数、余白、ずれ 1,800 個での
  D-UNC、3 つの乗数での天井：失敗 0。査読者：$`\hat\zeta_A`$ での天井を証明で。反例の点は $`D`$ に入り $`X_{20}`$ より下。正規の乗数 743 個（$`\hat\zeta_H`$ より下で指数 $`\ge \hat G + G_2`$ のものは無い）、
  組 23,801 個での単調性：失敗 0。Lean の再実行は同じ。
- §2.2。10 個の段（1 から $`I_0`$ まで）での境目の鎖と標準形。4,768 回の試しで D-UNC$`^\pi`$ の実現の形。330 回の試しでずれ。標本 193 個で TAIL-LEVEL：失敗 0。Lean は緑。
  査読者：4,432 回の試しで包への所属、符号 483 個すべてで実現、131 回の試しと組 13,366 個で天井と単調性、$`D_\infty`$ への所属 1,110 個：失敗 0。著者の試しの再実行は同じ結果。
  Lean は緑で同じ出力。
- §2.3。新しい符号と頂上のパターン 17 個：パターンで、閉じていて、扇を持たず、鎖の数 2。証明書（再生した）：前向き 13 個中 12 個、$`\mathrm{CH}_3`$ より下の頂上 4 個中 3 個、
  追加 5 個中 4 個、逆向き 6 個中 0 個。名前の確かめ 62 個：失敗 0。Lean は緑。査読者：区域の自前の作り直し（上）、著者の実行はバイト単位で同じ、証明書 2 個を再現。Lean の再実行は同じ。

### 2.6 未解決

27 回目から 37 回目でこの一覧は変わった。今の一覧は [SHIFT9-ja.md](SHIFT9-ja.md) §3.6 にある。

- 上からの評価：$`\nu_C`$ について名前の付いた 1 つの組での (P) と (Q′)。(P) には $`G(\hat\zeta_H)`$ より先の蓋と、符号 $`P'`$ での下からの評価が要り、(Q′) には $`L(\omega)`$ の等最小の
  パターンが要る。$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価。
- FRAG のもとで $`X_{21}`$ より上の主張：$`D \gt \hat G`$ での長いちょうどの届く先（$`\Phi^{\hat G}`$ より下はあらすじ。その先は添字 $`\theta_2 + 1`$ での PSI-θ）。$`\hat\zeta_H`$ より先とどの $`\Omega_k`$ でも
  READ$`^\sharp`$。符号 $`G(\hat\zeta_A)`$ でのちょうどの届く先。$`\Omega_3`$ より上の層の下からの評価の側。
- 最初の到達不能基数：$`\varepsilon_0`$ より先の素の区域の符号、非可算の段階の札、$`\Omega_\omega`$ 以上の札。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準形の行列での段。
- $`\nu_C = \nu_S`$：LOW（符号が $`[G(\hat\zeta_H), P')`$ での CAP-0）。LOW$`^\infty`$。動く原子のある長い前置きのピン。$`G_2^2`$ 以上の符号での TC⁺。置くための $`G(\hat\zeta_3)`$ 以上の
  符号での蓋。(D1b)、(E4)。
- 名前：$`R(\Theta_{d\omega})`$；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ；届く先を符号で書く InaccPsi の式；$`X_{21}`$ より先の名前；
  [COVER-ja.md](COVER-ja.md) §9 の残り。
