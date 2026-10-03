[← Back](README-ja.md) | [English](REACHES.md) | [Japanese](REACHES-ja.md)

# $`\Xi_\omega`$ より上の $`R_2^+`$：正確な届く先、骨組み型の範囲、長さ 3 の最小の鎖

このページは [RESTARTS-ja.md](RESTARTS-ja.md) の続き。状態の言葉は [README-ja.md](README-ja.md) の §3 と同じ：
**証明済み**は、独立した査読者が、致命的な点も止める点も無く証明済みと判定したもの。このページの結果はどれも
2026-10 のもの。「査読 1 回」は査読者 1 人。「査読 2 回」は、独立した 2 つの論文がその結果を証明し、それぞれが
1 回ずつ査読されたこと。次の回の結果（相対化したピン、$`\Theta_A`$ までの正確な届く先、$`\Lambda_\varepsilon`$ までの名前、
長さ 3 の鎖のいちばん下）は 4 ページ目 [PINS-ja.md](PINS-ja.md) に、その次の 2 回の結果は 5 ページ目 [BREAK-ja.md](BREAK-ja.md) にある。
それによってここのいくつかの状態が変わった。
変わった所には印を付けた。

**記号。** [RESTARTS-ja.md](RESTARTS-ja.md) と同じ：$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$、届く先
$`\mathrm{lh}(\alpha) = \max\{\gamma : \alpha \le_1 \gamma\}`$、$`\omega^2`$ の 0 でない倍数 $`\lambda`$ に対するやり直しの点 $`\rho_\lambda = \upsilon_\lambda`$、
その最初のブロックの上端 $`\delta_\lambda = \upsilon_{\lambda+\omega+1}`$、$`\iota \mapsto \upsilon_\iota`$ の $`\alpha`$ 番目の 0 でない不動点 $`\Xi_\alpha`$。
「$`R`$ で」は $`R_2^S`$ でも $`R_2^C`$ でも、の意味。$`\mathrm{logend}(\alpha)`$ は $`\alpha`$ のカントール標準形の最後の項の指数。
$`C^*_3 = \{c_0 \lt c_1 \lt c_2\}`$ は $`R_2^C`$ の長さ 3 の最小の鎖、$`m_3 = \min\{m : m \le_1 c_0\}`$。

## 1. やり直しの点の正確な届く先

**$`\upsilon`$ の上のヴェブレン階層。** $`V_1(\alpha) = \Xi_\alpha`$（$`\alpha \ge 1`$）。$`V_{\gamma+1}`$ は $`V_\gamma`$ の不動点を並べたもの。
極限の $`\gamma`$ では、$`V_\gamma`$ は共通の不動点を並べたもの。やり直しの添字 $`\lambda`$ の段 $`\gamma(\lambda)`$ は、$`\lambda`$ が $`V_\gamma`$ の
値域に入る最大の $`\gamma`$（$`\lambda`$ が $`\iota \mapsto \upsilon_\iota`$ の不動点でなければ $`0`$）。$`\Lambda_\Gamma`$ は、すべての $`\gamma \lt \lambda`$ で
$`V_\gamma`$ の値域に入る最小の $`\lambda`$。

**再帰的なずれ $`O(\lambda)`$**（$`\mu \lt \lambda`$ の $`O(\mu)`$ から定める）。ずれの項 $`t`$ とは、1 つの変数 $`x`$ と定数から、和と
$`t \mapsto \omega^t`$ で作ったカントール標準形、または項 $`\varepsilon_{x+1}`$。やり直しの点 $`\rho_\mu`$ が $`t`$ を実現するとは
$`O(\mu) \ge t(\rho_\mu)`$ のこと。$`O(\lambda)`$ は、$`\lambda`$ の下で共終に多くのやり直しの点が実現する項 $`t`$ についての
$`t(\rho_\lambda) + 1`$ の上限。$`\Lambda_\varepsilon`$ は、その下で $`\varepsilon_{x+1}`$ が共終に実現される最小の $`\lambda`$。

- **定理 BLK$`^O`$**（証明済み、査読 1 回）。どのやり直しの添字 $`\lambda \lt \Lambda_\varepsilon`$ でも、定理 BLK$`^\Xi`$
  （[RESTARTS-ja.md](RESTARTS-ja.md) §3）の (i)–(iii) が $`\upsilon_{\lambda+\omega^2}`$ より下で $`R`$ で成り立ち、届く先は正確に
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + O(\lambda)`$。上端（補題 TOP$`^O`$）は FRAG を使わない。下端（補題 RS$`^O`$）は FRAG を使う。
  証明を支える新しい補題は 2 つ。**EXACT**：Wilken の基の付け替え $`\pi`$ はずれの項をちょうど動かす、
  $`\pi(t(r)) = t(s)`$（Wilken, APAL 145 (2007) 130–161, Lemma 4.2 と Def 5.1）。**IMG**：ずれの項を被覆で写したものは、
  新しい基での同じ項より小さくない（Wilken, APAL 145 (2007) 162–175, Thm 2.2）。写す先は $`O`$ の定義にある共終性で
  選んだやり直しの点なので、前の見取り図 RS$`_\lambda`$ の誤りは起きない。
- **系 EQB$`^O`$**（証明済み、査読 1 回）。$`R_2^S`$ と $`R_2^C`$ は $`\Lambda_\varepsilon`$ より下のすべての組で一致する。だから最初の違い
  $`\beta_0`$ は $`\Lambda_\varepsilon`$ 以上。
- **定理 OFF-V**（証明済み、査読 1 回）。どのやり直しの添字 $`\lambda \lt \Lambda_\Gamma`$ でも：$`\gamma(\lambda) = 0`$ で
  $`\lambda = \lambda_0 + \omega^e`$ なら $`O(\lambda) = -1 + e`$。$`\gamma = \gamma(\lambda) \ge 1`$ で $`\lambda = V_\gamma(\alpha)`$ なら
  $`O(\lambda) = \rho_\lambda\cdot\gamma + \mathrm{logend}(\alpha)`$。また $`O(\Lambda_\Gamma) = \omega^{\rho\cdot 2}`$。だから $`\Lambda_\Gamma \lt \Lambda_\varepsilon`$。
- **補題 RS$`_\lambda`$**（証明済み、査読 2 回）。どのやり直しの添字 $`\lambda \le \Xi_\omega`$ でも、$`R`$ で
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^*(\lambda)`$。これは BLK$`^O`$ と OFF-V から出る。もう 1 つの証明は §3 の定理 EXACT。
- **定理 EXACT と OFF-k**（証明済み、査読 1 回。正確な届く先の、独立したもう 1 つの証明）。基の付け替えで定めた
  形式的なずれ $`c^+`$ で、$`\lambda \lt \Theta_P`$ のすべてで $`R`$ で $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^+(\lambda)`$。ここで $`\Theta_P`$ は
  $`c^+(\lambda) \ge \varepsilon_{\rho_\lambda+\omega}`$ となる最小の $`\lambda`$。上からの評価は FRAG を使わない（新しい補題 PIN。上の Wilken の
  Thm 2.2 から）。下からの評価は FRAG を使う。$`\Theta_{add} = V_\omega(1)`$（すべての $`V_k`$、$`k \lt \omega`$ の最小の共通の不動点）
  までの $`c^+`$ の閉じた形は OFF-V と同じで、$`c^+(\Theta_{add}) = \rho\cdot\omega`$。だから正確な届く先とその閉じた形は、
  $`\lambda \le V_\omega(1)`$ のすべてのやり直しの添字で **査読 2 回**。証明済みの大小：$`\Xi_\omega \lt V_\omega(1) \lt \Theta_P`$。$`\Theta_P`$ を越えて、
  $`\Theta_1`$ まで（査読 2 回）と $`\Theta_A`$ まで（査読 1 回）延びた（[PINS-ja.md](PINS-ja.md) §2）。

| $`\lambda`$ | $`O(\lambda)`$ | $`\lambda`$ | $`O(\lambda)`$ |
|---|---|---|---|
| $`\omega^3,\ \omega^4,\ \omega^\omega`$ | $`2,\ 3,\ \omega`$ | $`\Phi_1 = V_2(1)`$ | $`\rho\cdot 2`$ |
| $`\omega^{\Xi_\omega+1}`$ | $`\Xi_\omega + 1`$ | $`V_2(\omega)`$ | $`\rho\cdot 2 + 1`$ |
| $`\Xi_n`$（$`1 \le n \lt \omega`$） | $`\rho`$ | $`V_3(1)`$ | $`\rho\cdot 3`$ |
| $`\Xi_\omega`$ | $`\rho + 1`$ | $`V_\omega(1)`$ | $`\rho\cdot\omega`$ |
| $`\Xi_{\omega^\omega}`$ | $`\rho + \omega`$ | $`\Lambda_\Gamma`$ | $`\omega^{\rho\cdot 2}`$ |

$`\lambda = \omega^{\Xi_\omega+1}`$ でずれの補題が成り立たなかった件は解決した：そこでは $`O = \Xi_\omega + 1 = -1 + e`$。
[RESTARTS-ja.md](RESTARTS-ja.md) §2 の予想 CAP は、段 0 のすべてのやり直しの点で OFF-V と一致し、$`\Xi_\omega`$ で外れる
（CAP は $`\rho`$ を出すが、届く先は $`\rho + 1`$）。

## 2. $`R_2^C`$ の核と $`\Phi_1`$ までの名前

- **定理 CORE-C$`^O`$**（証明済み、査読 1 回。FRAG 無し）。$`[0, \Lambda_\varepsilon) \subseteq \mathrm{Core}(R_2^C)`$。系（証明済み、査読 1 回）：
  $`\Lambda_\varepsilon \lt \Omega_1`$（査読者が引用を直したあと：Carlson 2009 の Lemma 15.11、Thm 14.14、Cor 15.15）、
  $`\min C^*_3 \ge \Lambda_\varepsilon`$、$`m_3 \ge \Lambda_\varepsilon`$、$`\kappa_S \ge \Lambda_\varepsilon`$。
- **定理 CORE-C$`^+`$**（証明済み、査読 1 回。FRAG 無し）。$`[0, \rho_{\Theta_P}) \subseteq \mathrm{Core}(R_2^C)`$。この区間で $`R_2^C`$ は
  $`R_2^S`$ と同じ組とブロックを持ち、（FRAG を使えば）$`R_2^S`$ と等しい。だから $`\beta_0 \ge \rho_{\Theta_P}`$。今は
  $`[0, \rho_{\Theta_A+\omega^2})`$ まで延びた（[PINS-ja.md](PINS-ja.md) §2）。
- **定理 T++**（証明済み、査読 3 回。3 つ目の証明は [PINS-ja.md](PINS-ja.md) §3 の定理 GEN）。$`\Xi_\alpha = \alpha`$ となる最小の $`\alpha \ge 1`$ を $`\Phi_1`$ とする。これは $`V_2(1)`$。
  $`1 \le \alpha \lt \Phi_1`$ で：
  $`\Xi_\alpha = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot\alpha)`$、そして $`x \lt \Xi_{\alpha+1}`$ で
  $`\upsilon_{\Xi_\alpha + x} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot\alpha + \theta\cdot x)`$。
  特に $`\Xi_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1})`$（前の予想）、$`\Xi_\omega = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1+1})`$。
  $`\Xi_1`$ より上の補題 REL は等式になる。道具：補題 SUB と包の補題 HL（1 つ目の論文）。補題 GAP、すなわち包
  $`\mathrm{Cl}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot(z+1), s)`$ の可算な部分は $`s`$ より下に留まる（2 つ目の論文）。
- **定理 PHI**（証明済み、査読 2 回。2 つ目の証明は [PINS-ja.md](PINS-ja.md) §3）。$`\Phi_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$。
- だから **$`R_2^C`$ で Wilken の主張は $`[0, \Phi_1]`$ で成り立つ**。両方の半分とも：そこのどの順序数も核に入り、
  つぶす関数の引数がどれも $`\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2} \lt I_\omega`$ 以下の InaccPsi の標準形の値になる
  （査読 2 回）。前は $`[0, \Xi_1]`$。今は $`[0, \Lambda_\varepsilon)`$ で成り立つ（[PINS-ja.md](PINS-ja.md) §3）。
- **$`\Xi_1`$ より下を InaccPsi の項で**（証明済み、査読 1 回。[RESTARTS-ja.md](RESTARTS-ja.md) §5 の予想 42+.I は、ここでは
  定理になった）。$`A = \omega^{\theta+a_1} + \cdots + \omega^{\theta+a_k}`$（$`a_1 \ge \cdots \ge a_k = e \ge 2`$）とすると：組は
  $`\psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1}\cdot j) \lt_2 \psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1}\cdot j + \theta)`$、
  やり直しの点は $`\psi_{\Omega_1}(\Omega_\omega + A)`$、その届く先は $`\psi_{\Omega_1}(\Omega_\omega + A + \omega^{\theta+1} + \theta) + (-1 + e)`$。
- **予想、今は証明済み**（[PINS-ja.md](PINS-ja.md) §3。NAME-OFFSET は直した形で）。NAME-V：$`V_\gamma(\alpha) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot\gamma}\cdot\alpha)`$（$`\gamma \ge 1`$）。NAME-OFFSET：
  $`\rho_\lambda`$ の名前の最後の項が $`\omega^{\theta+e}`$ なら、$`O(\lambda)`$ は $`-1 + e`$ の $`\Omega_1`$ を $`\rho_\lambda`$ に置き換えたもの。
  これらから $`\Lambda_\Gamma = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1^2})`$、
  $`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$。

## 3. 骨組み型の範囲（定理 SKEL）

届く先が自分の領域を出る最小のやり直しの添字 $`\lambda`$（$`\mathrm{lh}(\rho_\lambda) \ge \rho_{\lambda+\omega^2}`$）を $`\Lambda^*`$ とし、
$`\nu_P = \upsilon_{\Lambda^*+\omega^2}`$ とおく。

- **定理 SKEL**（証明済み、査読 1 回。$`R_2^S`$。FRAG 無し）。$`\Lambda^*`$ は存在して可算。$`\nu_P`$ より下で：
  (i) $`\lt_2`$ の組はちょうど $`\mathrm{logend}(\xi) = 1`$ の $`(\upsilon_\xi, \upsilon_{\xi+1})`$。(ii) やり直しの点は $`\lt_1`$ の前の元も
  $`\lt_2`$ の後の元も持たない。その届く先は自分の領域の中にあり、閉じている（やり直しの点と届く先の間のどの点も、
  届く先はそこまで）。(iii) ほかの点は上端 $`d`$ のブロックに入り、届く先は $`R_1^+`$ の届く先と $`d`$ の小さい方。
  (iv) $`R_2^S`$ は $`[0, \nu_P]`$ で骨組み型。$`\nu_P`$ でこの記述が初めて崩れる：$`\rho_{\Lambda^*} \lt_1 \nu_P`$。新しい道具の補題 C′
  は、届く先がどのブロックにあってもよいとするので、届く先の値は要らない。ほかに証明済み：$`\Theta_P \le \Lambda^*`$。
  $`R_2^S`$ のどの鎖 $`c_0 \lt_2 c_1 \lt_2 c_2`$ も $`c_0 \ge \nu_P`$。
- **未証明。** $`[\rho_{\Theta_P}, \nu_P)`$ の $`R_2^C`$：未解決の仮定 HC（$`\Lambda^*`$ より下のどのやり直しの点も、$`R_2^C`$ の届く先が
  $`R_2^S`$ の届く先以下）の下での概略だけ。$`[\Theta_P, \Lambda^*]`$ の正確な届く先：一般の移し方の形の下からの評価は
  証明済み（FRAG を使う）。上からの評価には、Wilken が予告した（APAL 145 (2007) 162–175, p. 174）$`R_1^+`$ の相対化した
  核が要るが、その論文は手元に無い。今は：その核は作り直され、正確な届く先は $`\Theta_A`$ まで分かり、HC は $`\Theta_A`$
  より下で成り立ち、$`R_2^C`$ は $`[0, \rho_{\Theta_A+\omega^2})`$ で分かった（[PINS-ja.md](PINS-ja.md) §1–2）。
- **予想**（プログラムで確かめた）。$`\upsilon_{\Lambda^*} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2})`$、ここで
  $`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$。これは行列 (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,2,0)(3,3,1)(3,0,0)(3,0,0) の点。
  $`\nu_P = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$。

## 4. 骨組みが終わる所

ある集合の上で $`R_2^+`$ が骨組み型とは：(SK1) $`\upsilon`$ の点でない点はそこで $`R_1^+`$ の届く先を持ち、(SK3) $`\lt_2`$ の組は
どれも $`(\upsilon_\xi, \upsilon_{\xi+1})`$（[RESTARTS-ja.md](RESTARTS-ja.md) §2）。$`R_2^S`$ と $`R_2^C`$ が骨組み型でなくなる最初の点を
$`\nu_S`$、$`\nu_C`$ と書く。INC1-nonups は「$`a`$ が $`\upsilon`$ の点でなく、$`R_2^C`$ で $`a \le_1 b`$ なら、$`R_1^+`$ でも $`a \le_1 b`$」
という命題。はじめは $`\upsilon_{\Xi_\omega+\omega^2}`$ より下で証明された。INC1-S は、$`R_2^S`$ とすべての $`a`$ についての同じ命題。
どちらも今はどこでも証明済み（定理 INC1、査読 1 回、[BREAK-ja.md](BREAK-ja.md) §1）。

**状態の変更**（次の回に見つかった止める点、[PINS-ja.md](PINS-ja.md) §4）。$`R_2^S`$ での LEFT の証明は、$`R_2^S`$ の言語での
$`\Sigma_1`$ 初等性から $`R_1^+`$ の $`\le_1`$ が出ると仮定していたが、出ない。だから LEFT と、それを使う下の結果（3CH、
FIRST-BREAK、FRAG2-W、FRAG2-C、§5 の C3′-FALSE）は、$`R_2^S`$ では INC1-S を仮定したときだけ成り立つ。
**2 度目の状態の変更**（[BREAK-ja.md](BREAK-ja.md) §1、査読 1 回）。LEFT は、最初の悪い右端より下のどの左端でも成り立つ。
それは $`R_2^S`$ では $`\nu_P`$ より上。予想 NOBAD を仮定すれば（$`R_2^C`$ では CC も）どこでも成り立つ。FIRST-BREAK と 3CH (iv) は
また条件なしになった。ほかの結果は NOBAD を仮定して成り立ち、十分下では条件なしで成り立つ。
**3 度目の状態の変更**（[BREAK-ja.md](BREAK-ja.md) §1、査読 1 回）。NOBAD、INC1-S、INC1-nonups は証明済み。だから LEFT と、
それを使う下のどの結果も、今は仮定なしで成り立つ。

- **補題 LEFT**（はじめは $`R_2^S`$ では INC1-S、$`R_2^C`$ では INC1-nonups を仮定して証明済み、査読 1 回。今は証明済み、上を見よ）。$`\lt_2`$ の左端はどれも $`\lambda`$ が
  極限の $`\upsilon_\lambda`$。**系 3CH**：どの鎖 $`c_0 \lt_2 c_1 \lt_2 c_2`$ でも、$`c_0 = \upsilon_\Lambda`$（$`\Lambda`$ はやり直しの添字）、
  $`c_1 = \upsilon_\mu`$（$`\mu`$ は極限）。だから $`\nu_S \le c_1`$。
- **定理 FIRST-BREAK**（証明済み、査読 1 回。[BREAK-ja.md](BREAK-ja.md) §1 で条件なし、査読 1 回。$`R_2^S`$）。$`\nu_S = \min(\nu_a, \nu_b)`$。ここで $`\nu_a`$ は $`\upsilon_\lambda \lt_2 b`$ かつ
  $`b \ne \upsilon_{\lambda+1}`$ となる最小の $`b`$。$`\nu_b`$ は、$`\upsilon`$ の点 $`u`$ の届く先 $`\mathrm{cap}(u)`$ が、$`\upsilon`$ の点でない点 $`a`$ の $`R_1^+`$ の
  届く先を切る（$`u \lt a \le \mathrm{cap}(u) \lt \mathrm{lh}_1(a)`$）ような最小の $`\mathrm{cap}(u) + 1`$。ほかに証明済み：$`\nu_S \gt \nu_P`$（§3）。
- **骨組みは $`m_3`$ より下で終わる**（証明済み、査読 2 回）。定理 NU-C：$`\upsilon_{\Xi_\omega+\omega^2} \le \nu_C \lt m_3`$。「2 つの
  $`\lt_2`$ の後の元を持つ点」というパターンは長さ 3 の鎖を持たないので、DOM₂ によりその最小の実現は $`m_3`$ より下。
  補題 FAN（両方の構造、FRAG 無し）：鎖 $`d_0 \lt_2 d_1 \lt_2 d_2`$ と、$`m \le_1 d_0`$ となる $`m \lt d_0`$ に対し、2 つの
  $`\lt_2`$ の後の元を持つ点は $`m`$ の下で共終。だから長さ 3 の鎖は、骨組み型でない最初の点では始まらない。
- **再生した証明書から**（$`R_2^C`$。証明済み、査読 1 回）。2 つの $`\lt_2`$ の後の元を持つ点はどれも、$`\Phi_3(\mathrm{SRO})`$ の点より上。
  $`\nu_C`$ は [README-ja.md](README-ja.md) §6 の表の 28 行目の $`\Phi_3`$ の点より下：はじめは INC1-nonups を仮定して、今はどんな
  仮定もなしで（[BREAK-ja.md](BREAK-ja.md) §2）。
- **骨組みの外での基の付け替え**（書かれた仮定の下で証明済み、査読 1 回、FRAG を使う）。FRAG2-W：定理 FRAG2 は SK1
  だけで足りる。FRAG2-C：追加のデータ $`\mathrm{Cut}(a) = \min\{\mathrm{cap}(u) : u \text{ a } \upsilon\text{-point}, u \le_1 a\}`$ を使えば、届く先が
  「切られた骨組み型」の所で成り立つ。FRAG2-1E：任意の 2 つの $`\varepsilon`$ 数の基の間の 1 回の付け替え（Wilken の
  $`\iota_{\tau,\alpha}`$ の $`R_2^+`$ 版）、Wilken の付帯条件の下で。LEFT により $`\lt_2`$ の左端は $`\upsilon`$ の点だけなので、ほかの基は
  $`\le_1`$ のデータしか持たない。FRAG2-W と FRAG2-C は INC1 も仮定していたが、それは今は証明済み（[BREAK-ja.md](BREAK-ja.md) §1）。**未証明**（止める点）：範囲の主張「FRAG2-W は $`\nu_b`$ まで」と「$`\nu_b`$ より先も切られた
  骨組み型」。証明は SK3 を仮定するが、それは $`\nu_a`$ より上で成り立たない。査読者の直し方：$`[0, \nu_S)`$ に制限する（$`\nu_S`$ は今は
  正確に分かっている、[BREAK-ja.md](BREAK-ja.md) §2）。
- **予想 NS。** $`\nu_S = \nu_C`$ は「入れ子の組を持つ組」の最小のものの上端で、$`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ と
  $`\psi_{\Omega_1}(\omega^{\Omega_\omega+1})`$ の間、$`\theta_0`$ よりはるかに下。最初の到達不能基数は、2 つの $`\lt_2`$ の後の元を持つ最初の点で
  初めて入る。今は：$`R_2^S`$ では「$`\nu_S`$ は入れ子の組を持つ最小の組の上端」が証明済み（定理 FIRST-PAIR、査読 1 回、
  [BREAK-ja.md](BREAK-ja.md) §2）。その名前（$`\theta' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$ として $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'+1} + \theta')`$、予想した
  区間の中）は予想のまま。$`R_2^C`$ では $`\nu_C = T_C \le \nu_S`$ で、$`R_2^C`$ に余分な「幽霊」の組が 1 つある場合を除けば
  $`\nu_C = \nu_S`$（定理 NU-CT、査読 1 回、[BREAK-ja.md](BREAK-ja.md) §2）。$`\nu_C = \nu_S`$ は未解決。

## 5. 長さ 3 の最小の鎖

- **下界**（証明済み）。$`m_3 \ge \Lambda_\varepsilon \gt \Phi_1`$（§2、査読 1 回）。だから $`m_3 \gt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$。
  別の論文が、弱い $`m_3 \gt \upsilon_{\Xi_\omega+\omega^2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1+1} + \omega^{\theta+2})`$ を示す（査読 1 回）。
  鎖のいちばん下の形（今は条件なし）ともっと強い評価は [PINS-ja.md](PINS-ja.md) §4 にある。
- **発見的な形の C3′ は偽**（はじめは $`R_2^S`$ では INC1-S、$`R_2^C`$ では INC1-nonups を仮定して証明済み、査読 1 回。今は条件なし、
  [BREAK-ja.md](BREAK-ja.md) §1）。$`\tau`$ の上の次のやり直し $`r_1(\tau)`$ は $`\tau`$ の上の最小の $`\upsilon`$ の点。
  その添字は後続なので、LEFT により $`\lt_2`$ の左端にならない。だからやり直した 3 点 $`\{r_1, r_\omega, r_{\omega+1}\}(\tau)`$ は決して
  鎖にならない。C3′ の数の形（[README-ja.md](README-ja.md) §3）は導き方を失った。予想としては残る。直した形 C3′′（予想）：
  あるやり直しの添字 $`\Lambda`$ で $`C^*_3 = \{\upsilon_\Lambda, \upsilon_{\Lambda+\omega}, \upsilon_{\Lambda+\omega+1}\}`$。査読者は反対の材料を挙げた：
  + の無い $`R_2`$ では、最小の鎖の添字は $`(\Lambda, \Lambda\cdot\omega, \Lambda\cdot(\omega+1))`$（Wilken 2021）。今は
  C3′′ は偽（定理 C3′′-FALSE、査読 1 回、条件なし、[BREAK-ja.md](BREAK-ja.md) §3）。
- **NO-GEN**（証明済み、査読 1 回。$`R_2^C`$）。長さ 3 の鎖を持たない被覆されたパターンから生成される（Carlson 2009 の
  Defs 9.1、9.4、10.1、13.10、Thm 14.11）のは、それを持たないパターンだけ。だから鎖は種の中に無ければならない。
  Carlson が種を被覆されると示すのは Lemma 15.11 だけ（集合論、証人は $`\omega_1^{CK}`$ より上）。
- **GEN-OTP**（証明済み、査読 1 回。Carlson 2009 の 14.7–14.10、15.1 から）。長さ 3 の鎖の抽象的なパターンから公平に
  生成すると、順序数の始切片と同型な構造ができ、各 $`c_i`$ は $`i`$ 番目の種の点より下の順序型。だから C3′ の上半分は、
  この構造の順序数解析そのもの。
- **予想 MONO を仮定すると**（$`R_2`$ の $`\le_1`$ は $`R_1^+`$ の $`\le_1`$ に含まれる。証明済み、査読 1 回）：$`m_3`$ は $`\upsilon`$ の点か、
  $`c_2`$ は $`m_3`$ の上の最小の $`\upsilon`$ の点より下。
- **書かれた形では未証明**（止める点）：ずれ $`\rho\cdot k + c`$ に対する TOP$`_\lambda`$ の形。やり直しの点の上での $`\tau \lt_2 \delta`$ を
  仮定に足す必要があり、足せば証明済み。証明済みの評価はこれを使わない。$`\Lambda_\varepsilon`$ より下では TOP$`^O`$ がこれを含む。
- **予想。** OFFSET-W と BLK-GEN（ずれが $`\rho\cdot k + c`$ の形の間は骨組みが続く）。これらの下でも、骨組みの方法が届くのは
  せいぜい $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$ くらいで、$`\psi_{\Omega_1}(\varepsilon_{I_0+1})`$ よりはるかに下。

## 6. 確認

どれも 60 秒未満。どれも証明ではない。

- プログラム `phi3def2` で、$`\Xi_\omega`$ より上の標準形の行列 13 個：節を Wilken の Thm 2.2 で読むと、どの届く先も
  $`\delta + O(\lambda)`$（査読者の注：これらの節の値は、合う予測であって、プログラムが計算した値ではない）。査読者：新しい
  行列 10 個、すべて予測どおり。
- 証明書：25 個中 25 個を見つけて再生した（$`\Xi_\omega`$ からの続いた 9 点、16 組の $`M[N] \lt M`$）。逆向きは 9 個中 0 個。
  査読者がもう一度 25 個中 25 個を再生した。§4 のために、査読者が証明書 5 個を再生した。
- 名前：InaccPsi の項 21 個と 18 個。すべて標準形で、真に増える。Python と Lean で確かめた。査読者による $`\Xi_1`$ と
  $`\Xi_2`$ より下の標準形の乱択試験（約 190 万回）：補題 GAP の反例は 0。
- (0,0,0)(1,1,1)(1,1,0)(2,2,1) からの標準形の行列 598 個：プログラムのどの組も、左端の届く先は右端、2 つの組は
  入れ子にならない。やり直しの点の届く先が次のやり直しの点を越えるのは、ちょうど $`\Lambda^*`$ の行列から（40 パターン）。
  骨組みを崩す最初のプログラムのパターンは [README-ja.md](README-ja.md) §6 の表の 27 行目の $`\Phi_3`$
  （$`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$）。$`\Xi_\omega`$ からそこまでの 14,000 個を超えるパターンに 1 つも無い（調べた範囲は重なる）。

## 7. 未解決

- $`\Theta_A`$ より上の正確な届く先（$`T_\omega`$ より下のどの基の上でも、その基の上で走らせた形式的な届く先の再帰に従う。
  概略だけ、[BREAK-ja.md](BREAK-ja.md) §7.1）。$`\Theta_A`$ までの届く先と、$`[\Lambda_\Gamma, \Lambda_\varepsilon)`$ での $`O`$ の閉じた形は、今は
  証明済み（[PINS-ja.md](PINS-ja.md) §2–3）。
- $`\nu_C`$ より上の $`R_2^C`$（$`R_2^C`$ の核は今は $`\nu_C \gt \nu_P`$ で $`[0, \nu_C]`$ を含む、[BREAK-ja.md](BREAK-ja.md) §2）。INC1-nonups と INC1-S は今は
  証明済み（[BREAK-ja.md](BREAK-ja.md) §1）。
- $`\Theta_P`$、$`\Lambda^*`$、$`\nu_P`$、$`\nu_S`$ の値（$`\Lambda_\varepsilon`$ までの名前は今は証明済み、[PINS-ja.md](PINS-ja.md) §3。$`\nu_S`$ は今は正確に
  記述できたが、名前は予想、[BREAK-ja.md](BREAK-ja.md) §2。§7.3 で帰着）。
- $`\nu_S`$ より先の FRAG2：$`\upsilon`$ の点でない基をいくつも同時に（FRAG-E）、および入れ子の切るデータ。
- $`C^*_3`$：上半分（生成した構造の順序数解析）、下半分 $`m_3 \ge \psi_{\Omega_1}(\varepsilon_{I_0+1})`$、予想 CH。
- $`V_3`$ より上での変換器の順序の命題 S。
