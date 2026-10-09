[← Back](README-ja.md) | [English](SHIFT5.md) | [Japanese](SHIFT5-ja.md)

# $`R_2^+`$ の 25 回目：FRAG のもとで $`\nu_C \ge X_{19}`$、着地の蓋、$`G_2^2`$ より下の TC⁺、どの η でも GEN

このページは [SHIFT4-ja.md](SHIFT4-ja.md) の続き（そこの §2 が 24 回目）。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことの言い直しにすぎないと言った結果は、進みとして数えない。

3 つの論文（2026-10）。どれも 1 回ずつ査読された。だからこのページの結果は、回数を書いていなければ査読 1 回。**査読 2 回** とは、24 回目の査読者が
直しを出した（またはその結果を確かめた）うえで、この回の査読者が書き出したものをもう一度確かめたもの。どの論文も Wilken, JSL 72 (2007)、
Carlson, AML 38 (1999)、Wilken, AML 45 (2006)、Carlson 2009, p. 97 が予告する同値を使わない。ここで引く論文：[SHIFT4-ja.md](SHIFT4-ja.md) §1 と同じ [W07a]（L.3.30、L.4.7）
と [W07b]（L.2.1、Thm 2.2、Def 4.1、Thm 5.3 の証明）。Lean のファイルは足していない：2 つの論文（§1、§3）が項を比べるだけの Lean のファイルを確かめ（`#eval`、定理は無い。
緑で、査読者の再実行でも緑）、§2 の査読者も同じ種類のものを書いた（緑）。これらは確かめた扱い。24 回目の査読の細かい点は反映した：[SHIFT4-ja.md](SHIFT4-ja.md) §2.1 と §2.2 へのものは
§1 の論文が反映し、その査読者がもう一度確かめた（**査読 2 回**）。そこの §2.4 のラベルの点は §3 が片づけた。残りは [SHIFT4-ja.md](SHIFT4-ja.md) §2 に反映した。段の番号は
[SHIFT-ja.md](SHIFT-ja.md) と同じ（論文より 1 つ大きい）：段 1 は $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ より下。

記号は [SHIFT4-ja.md](SHIFT4-ja.md) と同じ：$`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$、$`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$、$`G_2 = G(\omega^2)`$、$`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$、
$`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$、そこの §2.2 の読み方 $`R`$、$`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$。この回の新しい名前（[SHIFT4-ja.md](SHIFT4-ja.md) §2.2 の $`\hat\zeta_2`$ とともに）：

```math
\hat\zeta_3 = \theta_3\cdot\omega^2,\quad g_3 = \psi_{\Omega_3}(\Omega_\omega + \hat\zeta_3),\quad \varepsilon_+ = \varepsilon_{G_2+1},\quad \hat\zeta_4 = \hat\zeta_3 + \omega^{\omega^{g_3\cdot 2}},\quad \hat\zeta_\varepsilon = \hat\zeta_3 + \varepsilon_{g_3+1}.
```

$`R(\hat\zeta_3) = G_2`$、$`R(\hat\zeta_4) = \omega^{G_2^2}`$、$`R(\hat\zeta_\varepsilon) = \varepsilon_+`$、$`\hat\zeta_2 \lt \hat\zeta_3 \lt \hat\zeta_4 \lt \hat\zeta_\varepsilon \lt \Omega_4`$（確かめた）。

## 1. 着地の蓋：FRAG のもとで $`\nu_C \ge X_{19}`$

- **[SHIFT4-ja.md](SHIFT4-ja.md) §2.1 と §2.2 への 24 回目の査読の細かい点を反映した**（証明済み、**査読 2 回**）。その中に：$`X_{18}`$ の証明の間違った段階を、最小の倍数の補題
  （$`e' \le e`$ なら、$`\gamma`$ より上の $`\omega^e`$ の最小の倍数は $`\ge \gamma + \omega^{e'}`$）で置き換えた。基 $`\eta \ge \Omega_2\cdot a`$ での D-UNC$`^{\mathrm{SEG}}`$（使っていたのに書いていなかった場合）。
  読み方の後者の段階を数える規則 PSI-n から導いた。尾の基を $`H(\Omega_3)`$ より上にとる。$`\tau_{\mathrm{LH}}`$ で分離しないという主張は注意にすぎない（下を見よ）。だからこれらの直しを入れた
  $`X_{17}`$ と $`X_{18}`$ の証明は **査読 2 回**（§2 の査読者も $`X_{18}`$ の証明の最後の段階をやり直した）。
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

- **未証明**（未解決）：$`\Omega_\omega`$ より下のどの正規の乗数でも着地の蓋（予想 READ$`^L`$。$`P'`$ より下のどの符号でも CAP-0 を与え、だから LOW を否定する）。
  $`D \ge \varepsilon_+`$ での長いやり直しのちょうどの届く先（あらすじ：[SHIFT2-ja.md](SHIFT2-ja.md) §1.1 の基の取りかえを通る同じ証明で、符号 $`G(\Omega_1)`$ まで）。$`G(\Omega_1)`$ より先では実現の読み方と
  蓋の読み方が違い、一般の分離は知られていない。LOW。(P)。(Q′)。
- 査読者のほかの細かい点：代わりの道は違う確かめを引いている（要るのは $`[\hat\zeta_3, \hat\zeta_4)`$ のどの指数も $`G_2^2`$ より下であることで、査読者の試しがそれを示す）。ある出力が
  $`X_{19}`$ でない点に「X19」と名札を付けている。$`\hat\zeta_\varepsilon`$ での天井は査読者の試しを引くこと。EXACT-LONG⁺ の越えの補題の 1 つの場合（$`D = 0`$）は別に定義すること。

## 2. $`\nu_C = \nu_S`$：$`G_2^2`$ より下の TC⁺ と、$`\omega^{G_2^2}`$ より下のまたぎ

記号は [SHIFT3-ja.md](SHIFT3-ja.md) §1.4 と §2.4 と同じ（TC⁺、LOW、LOW$`^\omega`$、(D1b)、(E4)）。$`\pi_\eta = \psi_{\Omega_2}(\Omega_\omega + \theta\cdot\eta)`$。この節の証明済みの結果はどれも段 1 でのもの。

- **D-UNC$`^\pi`$**（証明済み、FRAG 無し）。$`\eta \in D`$ と標準形 $`\xi \lt \pi_\eta`$ で：$`\eta + \xi \in D`$ ⟺ $`\xi`$ の定数が $`H(\eta + \xi)`$ より下。$`\eta`$ の項は吸い込まれてよい。
  （査読者：論文の言うのと違い、[SHIFT4-ja.md](SHIFT4-ja.md) §1.4 の D-UNC$`^Z`$ はこの場合ではない。$`\eta = 1, 2, \omega^2`$ ではずれ $`\xi = \pi_\eta \lt Z`$ が $`\eta + \xi \in D`$ を与え、D-UNC$`^\pi`$ はそれを含まない。）
- **BC$`^\pi`$**（段 1 で証明済み、FRAG 無し）。η の基の取りかえは、定数の無い上限 $`\Gamma \le \pi_\beta`$ より下のすべてのずれで定義され、行き先での吸い込みを許す。$`\nu_C = \nu_S`$ の
  設定ではどの基も $`H(\hat\zeta_2)`$ より上なので、$`\Gamma = G(\hat\zeta_2)`$ でよい。
- **READ-EQ**（証明済み）。基の取りかえは、$`G_2`$ より下の符号で読み方 $`\Theta`$ と入れ替えられる。これで [SHIFT3-ja.md](SHIFT3-ja.md) §1.4 の査読の細かい点が 1 つ片づく。
- **$`G_2^2`$ より下の TC⁺、MONO-F**（証明済み、FRAG のもと、段 1）。基の取りかえ $`B`$ は届く先を保つ（$`r(BR) = B(r(R))`$）：$`\tau \lt G_2`$ のどの短いやり直しでも、符号
  $`G_2\cdot D + m_0`$（$`D, m_0 \lt G_2`$）のどの長いやり直しでも、符号 $`G(\Omega_3)`$ でも。だから符号の移しはそのようなどの基の取りかえでも成り立つ。$`G_2^2`$ より下ではちょうどの届く先は符号について
  狭義増加。（査読者：どちらの半分にも FRAG が要る。論文の「≤ の半分は FRAG 無し」は間違い。）$`G_2^2`$ より先では上下からはさむ評価しか知られていない。
- **$`G(\hat\zeta_3)`$ より下の蓋をもう一度**（移しで証明済み、FRAG のもと）：§1 と同じ道で、$`G(\hat\zeta_3)`$ より下で CAP-0、$`\nu_C \ge X_{\hat\zeta_3} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_3 + \omega^{G(\hat\zeta_3)+1}\cdot 2)`$。これは $`X_{19}`$ より下の点。
  **未証明**：LOW が偽のときの対応する評価（段 2 でのこれらの蓋が要る）。（査読者：乗数が正規であることは欠かせない。正規でない $`\zeta \lt \hat\zeta_3`$ は $`R(\zeta) \ge G_2`$ になりうる。）
- **仮定つき。数えない**（LOW のもとで、FRAG のもとで正しい。論文は LOW$`^\omega`$ のもとで主張する）。η のずれが $`\omega^{G_2^2}`$ より下のどの (D1b) のまたぎでも：どの添字の不動点の先でも
  帳簿づけ、$`G(\hat\zeta_3)`$ より下での余地、$`G_2^2`$ より下の指数でのピンと遠い TOP-REG、記録したどのやり直しでも TC⁺（U0–U3）。だからこれらのまたぎは置ける（PLACE$`^{T2}`$、RES-ALL$`^{T2}`$）。
  $`c_u = H(\eta_u + \omega^{G_2^2})`$ は区域の系（ZONE$`^{(2)}`$）。**進行を止める点**：LOW$`^\omega`$ が足すのは $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ の場合だけで、予想した名前はこの場合を予言する。
  そこではこれらの段階に、長いやり直しのちょうどの届く先、CROSS-O とピン、$`G(\hat\zeta_3)`$ より下の蓋、LONG-CLASS、BC$`^\pi`$ の段 2 での形が要り、どれも証明されていない。だから
  [SHIFT3-ja.md](SHIFT3-ja.md) §1.4 の査読の進行を止める点（そこのすべてが LOW のもと）は残る。
- **残り**（論文の組み立て。LOW$`^\omega`$ を LOW に置き換え、あらすじの段階を 1 つ含む）。$`\nu_C = \nu_S`$ は次から出る：$`G_2^2`$ 以上の長い符号での、基の取りかえと入れ替えられるちょうどの
  届く先。$`G(\hat\zeta_3)`$ 以上の符号での蓋（余地）。TWIST のあとの点検（あらすじ）。LOW。§1 は $`D \lt \varepsilon_+`$ での長いやり直しのちょうどの届く先と $`G(\hat\zeta_\varepsilon)`$ より下の蓋を与えるが、それらが
  基の取りかえと入れ替えられることを示した論文は無い。$`\nu_C = \nu_S`$ も $`\nu_C \lt \nu_S`$ も **未解決**。
- 査読者のほかの細かい点：ピンでの引用 1 つ（READ-EQ ではなく区域の移し）。論文が使わないと言う辞書を 1 か所で使っている。最初の未解決の場合の符号は $`G_2^2`$ ではなく
  $`G_2^2 + 1`$。

## 3. どの η でも GEN、$`\psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$ までの素の符号

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

## 4. 25 回目のあとの状態

- $`R_2^C`$ での Wilken の主張：$`[0, X_4]`$ では FRAG 無しで、$`[0, X_{19}]`$ では FRAG のもとで（$`[0, X_{18}]`$ は査読 2 回）両方の半分とも成り立つ。核の側は $`[0, \nu_C]`$ で成り立つ。
  $`\nu_C`$ の InaccPsi による上からの評価は無い：名前の付いた組での (P) は未解決のまま。
- 届く先：$`\tau \lt G_2`$ のどの短いやり直しと $`D \lt \varepsilon_+`$ のどの長いやり直しでもちょうど分かる（FRAG のもと）。$`G(\hat\zeta_\varepsilon)`$ より下のどの符号でも蓋。
- 名前：$`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ より下のどの $`\upsilon`$ 点も名前 $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$ を持つ。
- $`\theta_0`$ より下の下からの評価のための計画：SRO より下の段は、標本の 3,166 個すべてですべての $`n`$ で成り立つ（変わらず）。素の符号で $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$、
  $`\iota(\mathrm{CH}_2) \ge \Theta_1`$。
- 上からの評価：$`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ の InaccPsi の項による評価はまだ無い。
- $`\nu_C = \nu_S`$：LOW は決まっていない。CAP-0 は $`G(\hat\zeta_\varepsilon)`$ より下のどの符号でも成り立つ（FRAG のもと）。TC⁺ は段 1 で $`G_2^2`$ より下で成り立つ。残り：(P1)、(D1b)、(E4)。

## 5. 25 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1。名前、標準形、読み方、順の鎖 $`X_{17} \lt X_{18} \lt \dots \lt X_{19}^- \lt X_{19} \lt H(\Omega_4) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ を Python と Lean で（緑）。正規の乗数 3,000 個の指数、
  余白、組 861,202 個での順、着地のずれ 2,400 個での D-UNC、天井、最小の倍数の補題：失敗 0。査読者：細かい蓋への反例。標本 611 個での $`\hat\zeta_\varepsilon`$ での天井。
  $`\hat\zeta_4`$ と $`\hat\zeta_\varepsilon`$ の近くの指数（組 30,338 個）。ずれ 1,572 個での D-UNC。組 198,787 個での余白：失敗 0。Lean の再実行と自前の Lean のファイルは緑。
- §2。層の上限、$`R(\hat\zeta_3) = G_2`$、乗数 1,039 個、ずれ 4,423 個（吸い込みのあるもの 1,532 個）での D-UNC$`^\pi`$、符号 388 個での原子の置き換え：失敗 0（Python だけ）。査読者：正規の
  乗数 238 個、段 3 の基でずれ 1,219 個での D-UNC$`^\pi`$：失敗 0。順の鎖の Lean のファイルは緑。
- §3。$`\Omega_\omega\cdot\omega`$ から $`I_\omega + \theta`$ までの 15 個の引数 $`A`$ での STEP の写像 $`B`$ と LOW-STEP の写像 $`E`$（組およそ 600 万個）、9 つの段の値 1,620 個での標準形の試し、2,016 回の試しでの
  D-UNC、標本 429 個での符号：失敗 0。$`E`$ の壊した変種 3 つは失敗する。Lean は緑。査読者：ほかの包での取り出し（8,012 回の試し）、$`H`$ と $`\pi`$ の狭義増加（組 25,440 個）、
  $`[P_\xi, \pi_\eta)`$ のずれでの D-UNC（792 回の試し）、$`A`$ に可算の原子を持つ $`B`$ と $`E`$（組およそ 600,000 個）：失敗 0。Lean の再実行は同じ。

## 6. 未解決

- 上からの評価：$`\nu_C`$ について名前の付いた 1 つの組での (P) と (Q′)。(P) には $`G(\hat\zeta_\varepsilon)`$ より先の蓋と、符号 $`P'`$ での下からの評価が要り、(Q′) には $`L(\omega)`$ の等最小の
  パターンが要る。$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価。
- FRAG のもとで $`X_{19}`$ より上の主張：$`D \ge \varepsilon_+`$ での長いやり直しのちょうどの届く先（$`G(\Omega_1)`$ まではあらすじ）。$`G(\Omega_1)`$ より先での分離。どの $`\Omega_k`$ でも着地の蓋（READ$`^L`$）。
  $`\Omega_3`$ より上の層の下からの評価の側。
- 最初の到達不能基数：$`\omega^\omega`$ 以上の素の段階、非可算の段階の添字、$`\Omega_{\omega+1}`$。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準形の行列での段。
- $`\nu_C = \nu_S`$：LOW（符号が $`[G(\hat\zeta_\varepsilon), P')`$ での CAP-0）、LOW$`^\omega`$（今は：§2 の道具の段 2 での形）、$`G_2^2`$ 以上の長い符号での TC⁺、置くための $`G(\hat\zeta_3)`$ 以上の
  符号での蓋、(D1b)、(E4)。
- 名前：$`R(\Theta_{d\omega})`$；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ；届く先を符号で書く InaccPsi の式；$`X_{19}`$ より先の名前；
  [COVER-ja.md](COVER-ja.md) §9 の残り。
