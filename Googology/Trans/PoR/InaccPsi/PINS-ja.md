[← Back](README-ja.md) | [English](PINS.md) | [Japanese](PINS-ja.md)

# $`\Lambda_\varepsilon`$ より先の $`R_2^+`$：相対化したピン、$`\Theta_A`$ までの届く先、$`\Lambda_\varepsilon`$ までの名前、長さ 3 の鎖のいちばん下

このページは [REACHES-ja.md](REACHES-ja.md) の続き。状態の言葉は [README-ja.md](README-ja.md) の §3 と同じ：**証明済み**は、
独立した査読者が、致命的な点も止める点も無く証明済みと判定したもの。このページの結果はどれも 2026-10 のもので、
4 つの論文から来ている。どの論文も 1 回ずつ査読された。「査読 1 回」は査読者 1 人。「査読 2 回」は、独立した 2 つの
論文がその結果を証明し、それぞれが 1 回ずつ査読されたこと。査読者が未証明と判定した命題は、その論文のほかの部分が
証明済みでも **未証明** に書く。4 つの論文はどれも Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006)
を使わない。次の 4 回の結果は 5 ページ目 [BREAK-ja.md](BREAK-ja.md) に、5 回目から 7 回目は 6 ページ目 [COVER-ja.md](COVER-ja.md)、8 回目から 10 回目は 7 ページ目 [FANFREE-ja.md](FANFREE-ja.md)、11 回目と 12 回目は 8 ページ目 [VEBLEN-ja.md](VEBLEN-ja.md) にある。それによってここのいくつかの状態が変わった。

**記号。** [REACHES-ja.md](REACHES-ja.md) と同じ。$`\upsilon`$ の点 $`\tau`$ に対し、$`\tau^\infty`$ は $`\tau`$ より上の最小の $`\upsilon`$ の点、
$`\mathrm{seg}(\tau) = [\tau, \tau^\infty)`$。やり直しの添字 $`\lambda`$ に対し、$`\sigma_\lambda = \upsilon_{\lambda+1} = \rho_\lambda^\infty`$、$`\sigma'_\lambda = \upsilon_{\lambda+2}`$。
$`\pi_{\sigma,\tau}`$ は Wilken の基の付け替え（APAL 145 (2007) 130–161, Def 5.1）、$`\pi_\mu = \pi_{\rho_\mu,\rho_\lambda}`$。$`c^+`$ は
[REACHES-ja.md](REACHES-ja.md) §1（定理 EXACT）の形式的なずれ、$`\Theta_P`$ は $`c^+(\lambda) \ge \varepsilon_{\rho+\omega}`$ となる最小の $`\lambda`$、
$`\Lambda^*`$ と $`\nu_P`$ は [REACHES-ja.md](REACHES-ja.md) §3 と同じ。新しく：$`\Theta_1`$ は $`c^+(\lambda)`$ が定まらない最小のやり直しの
添字 $`\lambda`$（ずれが $`\mathrm{seg}(\rho_\lambda)`$ を使い切った所）。$`c^\#`$ は $`c^+`$ を $`[\sigma, \varepsilon_{\sigma+\omega})`$ へ延ばしたもの（移す写像は
$`\sigma_\lambda`$ を $`\sigma_\mu`$ へ送り、$`+`$、$`x \mapsto \omega^x`$、$`\varepsilon`$ を保つ）。$`\Theta_A`$ は $`c^\#(\lambda)`$ が定まらない最小の $`\lambda`$。

## 1. $`R_1^+`$ の相対化したパターン

Wilken（APAL 145 (2007) 162–175, p. 174）は、手元に無い論文のために 3 つのことを予告している：$`R_1^+`$ の核が
$`\alpha \le_1 \infty`$ となる最小の $`\alpha`$ であることの別証明、相対化したパターン、順序数とパターンの間の一様な初等再帰的な
対応。1 つの論文が「初等再帰的」以外をすべて作り直した。

$`\tau`$-パターンとは有限集合の組 $`(A, B)`$ で、$`A \subseteq \tau`$（パラメータ）、$`\tau \in B \subseteq [\tau, \infty)`$。$`\tau`$-被覆は $`\le`$、$`+`$、
$`\le_1`$（前向き）を保つ。パラメータを上げてもよい（$`A`$ の上で $`h(a) \ge a`$、$`h(\tau) \ge \tau`$）。$`\mathrm{Core}^\tau`$ は、
$`\tau`$-最小同型なパターンの $`B`$ をすべて合わせたもの。

- **定理 RC-PIN**（証明済み、査読 1 回。$`\tau \in \{1\} \cup E`$）。どの $`z \in [\tau, \tau^\infty)`$ も、有限の $`\tau`$-パターンでピン留め
  される：その $`\tau`$-被覆はどれも、パラメータを上げるものも、$`h(z) \ge z`$ を満たす。ピンは Wilken の Thm 5.3 の証明
  （Claim 5.5(a)(ii) と 5.6）の中にもうある。1 つの区間の場合（$`\tau`$ が $`\upsilon`$ の点）は、別の論文が独立に証明した
  （補題 RP、査読 1 回）。だからこの場合は **査読 2 回**。
- **定理 RC**（証明済み、査読 1 回）。どの $`\tau \ge 1`$ でも $`\mathrm{Core}^\tau = \{\tau\text{-pinned points}\} = [\tau, \tau^\infty)`$。
  $`\tau \in \{1\} \cup E`$ ならこれは $`T^\tau \cap [\tau, \Omega_1)`$。
- **系 CORE1**（証明済み、査読 1 回）。$`\mathrm{Core}(R_1^+) = [0, \upsilon_1)`$。Carlson 2001 の Thm 5.12 を使わない（核の定義だけを
  使う）。これは Wilken の予告の 1 つ目。
- **定理 U**（証明済み、査読 1 回）。$`\sigma \lt \tau`$ を $`\upsilon`$ の点、$`z \in \mathrm{seg}(\tau)`$ とする。パラメータを動かさず、$`\le`$ と $`+`$
  を保ち、$`\tau`$ を $`\sigma`$ へ送り、$`\tau`$ より上の $`\le_1`$ の事実を保つ写像はどれも $`h(z) \ge \pi_{\sigma,\tau}(z)`$ を満たす。
  COMP-π（$`\pi_{\sigma,\tau} = \pi_{\sigma,\sigma'} \circ \pi_{\sigma',\tau}`$）と MON-π も証明済み。
- **定理 UNIF**（証明済み、査読 1 回）。$`\pi_{\sigma,\tau}`$ は、$`\tau`$-最小同型なパターンを $`\sigma`$-最小同型なパターンへ、$`R_1^+`$ の
  同型として写す。**対応** $`z \mapsto P^\tau(z)`$ と $`(P, b) \mapsto \nu^\tau(P, b)`$（$`P`$ の厳密な $`\tau`$-被覆 $`h`$ についての $`h(b)`$ の最小値）は
  互いに逆で、$`\pi`$ と交換する（証明済み、査読 1 回、厳密な被覆について）。**CL-UNIF**（証明済み、査読 1 回）：
  $`\{0, \tau, z\}`$ を成分、$`\mathrm{lh}`$、bar 演算で閉じたもの $`C_\tau(z)`$ は $`\pi`$ と交換する。
- **未証明。** UNIF が全射であること（引き戻したパターンの $`\tau`$-写しは $`\pi`$ の定義域から出うる）。パラメータを上げる
  被覆に対しても $`\pi[P^\tau(z)]`$ が $`P^\sigma(\pi z)`$ の役をすること。書かれた形での「$`C_\tau(z)`$ は $`\tau`$-最小同型なピンの
  パターン」（引用した定理は Carlson–Wilken, JSL 77 (2012) の被覆を使い、ここの被覆ではない）。最後のものは今は定理
  EXPL で証明済み（[BREAK-ja.md](BREAK-ja.md) §4、査読 1 回）。
- **未解決。** $`C_\tau(z)`$ がいつも有限か（CL-FIN）、だから対応が初等再帰的か。定義のままでは対応は計算できる形でない。
  今は CL-FIN は証明済み（[BREAK-ja.md](BREAK-ja.md) §4、査読 1 回）。「初等再帰的」は概略だけ。
  査読者の注：Carlson–Wilken 2012 の §3（Def 3.6、Thm 3.9(1)）に、核の中での相対化したパターンの理論がもうある。
  定理 RC はこの弱い概念での類似で、どの $`\tau`$ でも、核より上でも成り立つ。

## 2. $`\Theta_A`$ までの正確な届く先

- **補題 PIN\***（証明済み、査読 1 回。FRAG 無し）。独立に **IMG$`^T`$**（査読 1 回）としても見つかったので **査読 2 回**。
  やり直しの点 $`\lambda`$ での上からの評価に使う写しや被覆 $`h`$（$`\rho`$ より下のパラメータを動かさず、$`h(\rho) = \rho_\mu`$）は
  どれも、パラメータが動かない $`c \in \mathrm{seg}(\rho)`$ すべてで $`h(c) \ge \pi_\mu(c)`$ を満たす（補題 PIN のように
  $`c \lt \varepsilon_{\rho+\omega}`$ だけではない）。**CAP-PIN**：$`h(\sigma_\lambda)`$ は $`\sigma_\mu`$ 以上の $`\upsilon`$ の点。**PIN-A**：$`\sigma`$ の上の項で
  $`\varepsilon_{\sigma+\omega}`$ まで同じ。
- **定理 EXACT-1**（証明済み、査読 2 回）。どのやり直しの添字 $`\lambda \lt \Theta_1`$ でも、$`R`$ で
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^+(\lambda)`$。上からの評価は FRAG を使わず、下からの評価は FRAG を使う。また
  $`c^+(\Theta_P) = \varepsilon_{\rho+\omega}`$（査読 1 回）、$`\Theta_P \lt \Theta_1 \le \Lambda^*`$（査読 2 回）。
- **定理 EXACT-A**（証明済み、査読 1 回）。どの $`\lambda \lt \Theta_A`$ でも、$`R`$ で $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^\#(\lambda)`$。$`\Theta_1`$ では
  $`\mathrm{lh}(\rho_{\Theta_1}) = \delta + \sigma`$（下からの評価は査読 2 回）。$`\Theta_A`$ では
  $`\delta + \varepsilon_{\sigma+\omega} \le \mathrm{lh}(\rho_{\Theta_A}) \le \delta + \sigma'`$。下からの評価は FRAG と補題 FRAG-T（FRAG の写像は、ずれの項の上で
  $`+`$、$`x \mapsto \omega^x`$、$`\varepsilon`$ と交換する。FRAG を仮定して証明済み）を使う。
- **補題 ATTAIN**（証明済み、査読 1 回。組合せ的、FRAG 無し）。$`c^+`$ や $`c^\#`$ のどの値 $`t`$ も、$`c^+(\lambda) \ge t`$ となる最小の
  $`\lambda`$ でちょうど取られる。だから $`\Lambda_\Gamma \lt \Lambda_\varepsilon \lt \Theta_P \lt \Theta_1 \lt \Theta_A \lt \Lambda^*`$。
- **$`\rho_{\Theta_A+\omega^2}`$ までの $`R_2^C`$**（証明済み、査読 1 回）。定理 EQB-A：$`[0, \rho_{\Theta_A+\omega^2})`$ で $`R_2^C`$ は $`R_2^S`$ と同じ組、
  ブロック、上端を持ち、そこで（FRAG を使って）$`R_2^S`$ と等しい。ただし $`\varepsilon_{\sigma+\omega} \lt \xi \le \sigma'`$ での組
  $`(\rho_{\Theta_A}, \delta + \xi)`$ は除く。だから $`\beta_0 \ge \rho_{\Theta_A}`$。系 CORE-C$`^A`$（FRAG 無し）：
  $`[0, \rho_{\Theta_A+\omega^2}) \subseteq \mathrm{Core}(R_2^C)`$。そのうち $`[0, \rho_{\Theta_1})`$ は査読 2 回。[REACHES-ja.md](REACHES-ja.md) §3 の仮定 HC
  （やり直しの点の $`R_2^C`$ の届く先は $`R_2^S`$ の届く先以下）は、どのやり直しの添字 $`\lambda \lt \Theta_A`$ でも FRAG を使って
  成り立つ（査読者が直した形。下を見よ）。
- **反映による届く先**（証明済み、査読 1 回）。**INDEX**：やり直しの点での写しは、証人ごと運ぶどのブロックの $`\upsilon`$ の
  点も、添字をずらした点以上の $`\upsilon`$ の点へ送る。**TOP-FLAT$`_0`$**（FRAG 無し）と **REACH$`_0`$**（FRAG を使う）：
  反映されない最小の点 $`y_0 \ge \delta`$ が FLAT$`_0`$（$`[\rho, \delta_j]`$ の $`\upsilon`$ の点、$`\mathrm{seg}(\rho)`$ の点、$`\rho`$ より下の定数の和）に
  入るなら、$`\mathrm{lh}(\rho_\lambda) = y_0`$。プログラムの届く先 $`\delta_{n+1} + \tau_{n+1}`$ はこの形。**TOP-FLAT$`_1`$**（$`\rho`$ より上の
  1 つの区間）：補題 LHPAR\* と CL-FIN を仮定して証明済み、今は仮定なしで証明済み（定理 EXPL、[BREAK-ja.md](BREAK-ja.md) §4）。
- **条件付き**（FRAG と仮定 H-RC（その領域のどの区間でも、添字をずらすピンがある）を仮定して証明済み、査読 1 回）。
  どの $`\lambda \le \Lambda^*`$ でも、$`\rho_\lambda`$ の届く先は反映される点 $`y`$ についての $`y + 1`$ の上限で、$`\Lambda^*`$ は完全に反映される
  最小の $`\lambda`$。H-RC は最初の区間より先では未解決だったが、今は証明済み（補題 PIN-S、[BREAK-ja.md](BREAK-ja.md) §4、査読 1 回）。そして $`\nu_S`$ より下のどのやり直しでも成り立つ（[SHIFT-ja.md](SHIFT-ja.md) §9.1）。決めた添字の距離のどの区域にもわたって成り立つ（MULTI-RC\*、[SHIFT2-ja.md](SHIFT2-ja.md) §1.1）。$`\psi_{\Omega_2}(\Omega_2)`$ より下のどの η ずれを越えても成り立つ（MULTI-RC$`^U`$、そこの §2.1）。$`\psi_{\Omega_2}(\Omega_2^{\Omega_2})`$ より下でも成り立つ（そこの §3.1）。$`\psi_{\Omega_2}(\varepsilon_{\Omega_2+1})`$ より下でも成り立つ（[SHIFT3-ja.md](SHIFT3-ja.md) §1.1）。$`\theta`$ より下でも成り立つ（そこの §2.1）。
- **未証明**（止める点、1 文）：「HC は $`[0, \rho_{\Theta_A+\omega^2})`$ 全体で成り立つ」。$`\Theta_A`$ そのものでは上の評価しか分からず、
  EQB-A はそこで $`R_2^C \ne R_2^S`$ を許す。この文を使う定理は無い。今は $`\Theta_A`$ での届く先は $`\delta + \varepsilon_{\sigma+\omega}`$ なので、
  $`\lambda \le \Theta_A`$ のどこでも HC が成り立ち、$`[0, \rho_{\Theta_A+\omega^2})`$ で $`R_2^C = R_2^S`$（[BREAK-ja.md](BREAK-ja.md) §4、査読 1 回）。
- **予想**（名前は確認済み）：$`\Theta_P = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+\omega}})`$、
  $`\Theta_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$、$`\Theta_A = \psi_{\Omega_1}(\Omega_\omega + \varepsilon_{\theta+\omega})`$。$`\Theta_P`$ の名前は今は証明済み（査読 1 回、THETA-P、
  [FANFREE-ja.md](FANFREE-ja.md) §10.4）。$`\Theta_1`$ の名前は今は未解決の包の補題に帰着した（THETA1-RED、[VEBLEN-ja.md](VEBLEN-ja.md) §1）。さらに $`\Theta_1`$ と $`\Theta_A`$ の名前は、
  パラメータについての短い未解決の補題 1 つに帰着した（PAR-SAME、[VEBLEN-ja.md](VEBLEN-ja.md) §8。それが無いと証明に止める穴がある）。今は PAR-SAME が証明されたので、どちらの名前も証明済み
  （THETA1 と THETA-A、査読 2 回、[THETA-ja.md](THETA-ja.md) §1）。

## 3. すべての $`\upsilon`$ の点の名前（定理 GEN）

$`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$、$`D = \{\eta \lt \Omega_2 : \eta \in \mathrm{Cl}(\Omega_\omega + \theta\cdot\eta, H(\eta))\}`$ とおく。$`D`$ は
$`\Omega_\omega + \theta\cdot\eta`$ が標準形の引数になる $`\eta`$ の集合。可算な $`\eta`$ では、$`\eta \in D`$ と $`\eta \lt H(\eta)`$ は同じ。

- **定理 GEN**（証明済み、査読 1 回）。どの $`\eta \in D`$ でも $`H(\eta) = \upsilon_{1+\iota(\eta)}`$。ここで $`\iota(\eta) = \mathrm{otp}(D \cap \eta)`$。
  だから項 $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$（$`\eta \in D`$）は、$`\upsilon`$ の点を小さい順に並べる。ただし
  $`\upsilon^* = \sup H[D]`$ より下のものだけ：$`\upsilon`$ の点は $`\omega_1`$ の中で共終なので、すべてではない（訂正、[BREAK-ja.md](BREAK-ja.md) §3。
  GEN-EXT が $`\eta \lt \Omega_\omega\cdot\omega`$ まで延ばす、§2。今は $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ が証明済み、査読 1 回、[THETA-ja.md](THETA-ja.md) §1）。証明：後続では
  STEP と LOW-STEP、極限では CONT と、包の隙間についての一般的な補題 1 つ。すべての $`\eta \lt \Omega_2`$ で成り立つ。
  定理 T+、T++、PHI はその特別な場合。だから T+ は **査読 2 回**、T++ は **3 回**、PHI は **2 回** になった。
- **補題 GAP\*、SUP、DOWN、RI**（証明済み、査読 1 回）。RI：$`\iota(\eta)`$ がやり直しの添字であるのは $`\mathrm{logend}(\eta) \ge 2`$ の
  ときちょうど、後続であるのは $`\mathrm{logend}(\eta) = 0`$ のときちょうど。
- **定理 NAME-V**（証明済み、査読 1 回。[REACHES-ja.md](REACHES-ja.md) §2 では予想）。可算な $`g \ge 1`$ と $`\eta \in D`$ で：
  $`H(\eta)`$ が $`V_g`$ の値域に入るのは $`\mathrm{logend}(\eta) \ge \Omega_1\cdot g`$ のときちょうど。
  $`g, a \lt \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot g}\cdot a)`$ なら $`V_g(a) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot g}\cdot a)`$。だから
  $`\Phi_1 = V_2(1) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$、$`\Lambda_\Gamma = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1^2})`$。$`\Gamma`$ の点は
  $`H(\Omega_1^{\Omega_1}\cdot\beta)`$。別の論文が $`\Lambda_\Gamma`$ より下でこれらの名前を独立に証明した（定理 NAMES-Γ、査読 1 回：
  $`A = \Omega_\omega + \omega^{\theta+e_1} + \cdots + \omega^{\theta+e_m}`$、$`e_j \in [\Omega_1, \Omega_1^2)`$ の項 $`\psi_{\Omega_1}(A)`$ は、$`\Lambda_\Gamma`$ より下の
  $`\iota \mapsto \upsilon_\iota`$ の不動点をすべて並べ、その間では $`\upsilon_{\psi_{\Omega_1}(A)+x} = \psi_{\Omega_1}(A + \theta\cdot x)`$。また
  $`V_\omega(1) = \Theta_{add} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\omega^{\Omega_1+1}})`$）。だから $`\Lambda_\Gamma`$ より下の名前 $`V_g(a)`$ と $`\Lambda_\Gamma`$
  そのものは **査読 2 回**。
- **定理 NAME-OFFSET**（証明済み、査読 1 回。[REACHES-ja.md](REACHES-ja.md) §2 では予想）。やり直しの添字 $`\lambda`$ に対し、
  $`\iota(\eta_\lambda) = \lambda`$ となる $`\eta_\lambda \in D`$ をとり、$`e_\lambda = \mathrm{logend}(\eta_\lambda)`$ とおく。$`\lambda \lt \Lambda_\varepsilon`$ は
  $`\eta_\lambda \lt \varepsilon_{\Omega_1+1}\cdot\omega`$ と同じで、そのとき $`O(\lambda) = (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$。だから $`R`$ で
  $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$。また $`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$、
  $`O = \varepsilon_{\rho+1}`$ となる最初のやり直しの点は $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}})`$。これが $`[0, \Lambda_\varepsilon)`$ 全体での $`O`$ の
  閉じた形。$`\Lambda_\Gamma`$ より下では査読 2 回（NAMES-Γ も同じずれを出す）。
- だから **$`R_2^C`$ では Wilken の主張は $`[0, \Lambda_\varepsilon)`$ で成り立つ**、両方の半分とも（査読 1 回。$`[0, \Lambda_\Gamma]`$ では
  査読 2 回）：そこのどの順序数も核に入り、つぶす引数が $`\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1} \lt I_\omega`$ より小さい InaccPsi
  の標準形の値。前は $`[0, \Phi_1]`$。今は（査読 1 回）$`\Lambda' = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\zeta_{\Omega_1+1}+1}})`$ として
  $`[0, \rho_{\Lambda'+\omega^2})`$ で成り立つ（[FANFREE-ja.md](FANFREE-ja.md) §10.4）。さらに今は（査読 1 回）$`\Lambda_{\mathrm{fp}} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2)+1})`$ として
  $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$ で成り立つ（[VEBLEN-ja.md](VEBLEN-ja.md) §1）。さらに今は（査読 1 回）$`\Lambda_{\mathrm{fp}2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2\cdot 2)+1})`$ として
  $`[0, \rho_{\Lambda_{\mathrm{fp}2}+\omega^2})`$ で成り立つ（[VEBLEN-ja.md](VEBLEN-ja.md) §8）。
- **未証明で、しかも偽**（止める点、命題だけ）：著者の形「$`\lambda \lt \Lambda_\varepsilon`$ は $`e_\lambda \le \varepsilon_{\Omega_1+1}`$ と同じ」。
  査読者の反例：$`\eta = \varepsilon_{\Omega_1+1}\cdot\omega + \omega^2`$ は $`D`$ に入り $`e = 2`$ だが、$`\iota(\eta) \gt \Lambda_\varepsilon`$。直した形は上のもの。
  偽の向きを使うほかの結果は無い。
- **予想 NAME-OFFSET+。** $`\eta_\lambda \lt \theta`$ のすべてのやり直しの点で、同じずれの式が成り立つ。今は（査読 1 回）
  $`e_\lambda \le \varepsilon_{\zeta_{\Omega_1+1}+1}`$ で証明済み。$`\zeta_{\Omega_1+1}`$ は $`\Omega_1`$ より上の $`\alpha \mapsto \varepsilon_\alpha`$ の最小の不動点（NAME-OFFSET-Z、[FANFREE-ja.md](FANFREE-ja.md) §10.4）。さらに今は
  $`e_\lambda \le \psi_{\Omega_2}(\Omega_2) + 1`$ で証明済み。$`\psi_{\Omega_2}(\Omega_2)`$ は $`\Omega_1`$ より上の $`\alpha \mapsto \Gamma_\alpha`$ の最小の不動点（NAME-OFFSET-G、[VEBLEN-ja.md](VEBLEN-ja.md) §1）。さらに今は
  $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$ で証明済み。$`\psi_{\Omega_2}(\Omega_2\cdot 2)`$ はそのような 2 つ目の不動点（NAME-OFFSET-G⁺、[VEBLEN-ja.md](VEBLEN-ja.md) §8）。

## 4. 長さ 3 の鎖のいちばん下

INC1-S は「$`R_2^S`$ で $`a \le_1 b`$ なら $`R_1^+`$ でも $`a \le_1 b`$」という命題。INC1-nonups は、$`R_2^C`$ で $`a`$ が $`\upsilon`$ の点で
ないときの同じ命題（[REACHES-ja.md](REACHES-ja.md) §4）。$`U`$ は $`\upsilon`$ の点の集まり。

- **補題 LEFT の穴**（止める点。この回の査読者が見つけた）。$`R_2^S`$ での LEFT の証明（[REACHES-ja.md](REACHES-ja.md) §4）は、
  $`R_2^S`$ の言語での $`\Sigma_1`$ 初等性から $`R_1^+`$ での初等性が出る、と言う。これは誤り：$`R_1^+`$ の $`\le_1`$ はそれ自身を
  使って定義される（Carlson 2001, p. 19；Wilken 2020, pp. 418, 420）ので、$`R_2^S`$ での $`\Sigma_1`$ の写しは $`R_1^+`$ の $`\le_1`$ を
  保つとは限らない。だから LEFT とそれを使う結果は、$`R_2^S`$ では INC1-S を仮定したときだけ成り立つ（$`R_2^C`$ で
  INC1-nonups を仮定したときだけ成り立つのと同じ）。あとでどちらも予想 NOBAD に帰着し、
  今は INC1-S と INC1-nonups は証明済み（定理 INC1、査読 1 回、[BREAK-ja.md](BREAK-ja.md) §1）。だから LEFT、VEB、C3-VEB は仮定なしで
  成り立つ。
- **補題 PRINC-S**（証明済み、査読 1 回）。$`R_2^S`$ では、$`\lt_1`$ の左端と $`\lt_2`$ の右端は加法的主要数。
- **はしご**（証明済み、査読 1 回。補題 DIAG）。$`C_0 = U'`$、$`C_{l+1}`$ は $`C_l`$ の対角、極限の $`l`$ では $`C_l`$ は共通部分。
  $`C_1`$ は $`\iota \mapsto \upsilon_\iota`$ の不動点の集まり、$`C_2`$ は $`\alpha \mapsto \Xi_\alpha`$ の不動点の集まり。
- **補題 VEB**（はじめは $`R_2^S`$ では INC1-S、$`R_2^C`$ では INC1-nonups を仮定して証明済み、査読 1 回。今は条件なし、[BREAK-ja.md](BREAK-ja.md) §1。
  査読の小さな直し（1 つの場合）をまだ書き込んでいない）。$`y \lt f_1 \lt \cdots \lt f_n`$ で、
  すべての $`i`$ で $`y \lt_2 f_i`$ とし、$`b \lt y`$、$`a_i \lt \omega`$ で $`s = f_n\cdot a_n + \cdots + f_1\cdot a_1 + y\cdot a_0 + b`$ とおく。
  $`y \le_1 f_1 + s`$ なら $`y \in (C_l)^{(b)}`$。ここで $`l = \omega^n\cdot a_n + \cdots + \omega\cdot a_1 + a_0`$。例えば $`y \lt_2 e`$ と $`y \le_1 e + y`$
  から $`y = \upsilon_y`$ が出る。
- **定理 C3-VEB**（同じ状態）。どの鎖 $`c_0 \lt_2 c_1 \lt_2 c_2`$ でも：$`c_0 \in C_{\omega^\omega}`$ で、$`c_0`$ は $`C_{\omega^\omega}`$ の極限点。
  $`m \le_1 c_0`$ となる $`m \lt c_0`$ はどれも $`C_{\omega^\omega}`$ に入る。だから $`m_3`$ は $`\upsilon`$ の点で（予想 MONO は要らない）、$`\lt_1`$ の
  前の元を持たない。$`d \le_1 c_1`$ となる $`c_0`$ の $`\lt_2`$ の後の元 $`d`$ は $`\upsilon`$ の点。形 C3′′、
  $`C^*_3 = \{\upsilon_\Lambda, \upsilon_{\Lambda+\omega}, \upsilon_{\Lambda+\omega+1}\}`$ では：$`\Lambda = \upsilon_\Lambda`$ は $`(C_{\omega^\omega})'`$ に入り、$`\mathrm{lh}(c_1) = c_2`$、$`c_2`$ は
  $`c_1`$ のただ 1 つの $`\lt_2`$ の後の元、そして無限に多くの $`k`$ で $`c_0 \lt_2 \upsilon_{\Lambda+k}`$。C3′′ は偽
  （[BREAK-ja.md](BREAK-ja.md) §3）なので、これらの C3′′ の帰結は中身が無い。
- **未証明**（止める点）：「証明済みの定理が許す最小の $`\Lambda`$ は $`\Lambda_{struct}`$（$`C_{\omega^\omega}`$ の最小の極限点）」。これは定理
  SKEL（[REACHES-ja.md](REACHES-ja.md) §3：$`R_2^S`$ で $`c_0 \ge \nu_P`$）を見落としている。SKEL と C3-VEB から $`m_3 \ge \rho_{\Lambda^*}`$
  （査読者の議論）。だから評価は：$`\Lambda`$ は、$`\nu_P`$ 以上の $`(C_{\omega^\omega})'`$ の最小の元以上。予想した名前では
  $`\Lambda_{struct} \lt \Theta_P \le \Lambda^* \lt \nu_P`$（大小は Python と Lean で確認済み）なので、$`\Lambda_{struct}`$ は外れる。これらの構造からの
  評価はどれもまだ $`\theta_0`$ より下。今は $`\Lambda_{struct} \lt \nu_P`$ と「$`\Lambda_{struct}`$ では鎖が始まらない」が、名前も条件も
  使わずに証明済み（[BREAK-ja.md](BREAK-ja.md) §3、査読 1 回）。
- **証明書**（$`R_2^C`$。著者が 39 回の実行をすべて再生し、査読者が 7 つをもう一度再生した）。
  $`\Lambda \gt m_3 \gt`$ $`\Phi_3((0,0,0)(1,1,1)(2,2,2)(3,3,3))`$ の点、これは $`\Phi_3(\mathrm{SRO})`$ の点より上。[README-ja.md](README-ja.md) §6
  の予想「$`\Phi_3(\mathrm{SRO})`$ の点は $`\theta_0`$」が成り立てば $`m_3 \gt \theta_0`$。もっと強い「$`\Lambda \ge \Lambda_{cert}`$」（その点より上の
  $`C_{\omega^\omega}`$ の最小の極限点）は INC1-nonups が要ったが、それは今は証明済みなので成り立つ（[BREAK-ja.md](BREAK-ja.md) §1）。
- **予想、今は証明済み**（[BREAK-ja.md](BREAK-ja.md) §3、査読 1 回）。$`\min C_l = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot l})`$、
  $`\Lambda_{struct} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot\omega^\omega+1})`$。CH の下半分（$`m_3 \gt \psi_{\Omega_1}(I_0)`$）は未解決。「上半分は C3′′
  から」という道は無くなった。C3′′ は偽だから。数で書いた C3′ には
  $`\psi_{\Omega_1}(E + \theta)`$ が $`\iota \mapsto \upsilon_\iota`$ の不動点であることが要るが、そこで補題 REL が等号なら成り立たない。

## 5. 確認

どの実行も 60 秒未満。どれも証明ではない。

- ピン：パラメータと基 $`\tau \in \{1, \varepsilon_0, \varepsilon_1\}`$ を上げて $`z`$ を自分より下へ送る被覆を、$`\varepsilon_\omega`$ より下（そこでは
  $`R_1^+`$ の $`\le_1`$ は Wilken の Thm 2.2 で決まる）で探した。届く先の論文の証人の点を入れると、終わった 70 回の探索で
  反例 0（50 回は時間切れ）。成分、部分和、$`\mathrm{lh}`$ で閉じるだけでは足りない（120 中 57 で失敗）。RC-PIN はその閉包を
  使わない。
- 届く先：プログラム `phi3def2` で 11 個の標準の行列が届く先 $`\delta + \varepsilon_{\rho+\omega}`$、$`\delta + \sigma`$、$`\delta + \sigma + 1`$、
  $`\delta + \sigma + \rho`$、$`\delta + \omega^{\sigma+1}`$ を出す。査読者の新しい 2 個は $`\delta + \sigma\cdot 2`$ と、$`c \in \mathrm{seg}(\rho)`$ での
  $`\delta + \sigma + c`$ を出す。どれも EXACT-A の予言どおり（行列と添字の対応は類推による）。
- 名前：包の条件と標準形の判定を 4,004 個の引数で比べ、食い違い 0。3 つの種でそれぞれ 300 個の無作為な $`\eta`$（多くは
  $`\theta`$ 以上）：「標準形であることと、可算な部分がどれも $`H(\eta)`$ より小さいことは同じ」、食い違い 0。$`H`$ は約
  55,000 組で狭義単調増加。DOWN は 3,325 例。名前の付いた 22 個と 23 個の項は標準形で増加、Python と Lean で
  （試験のファイルで、証明ではない）。$`\Lambda_\Gamma`$ より上の 4 個の行列は NAME-OFFSET の予言する届く先を出す
  （材料にすぎない）。

## 6. 未解決

- $`\Theta_A`$ より上の正確な届く先：後の区間（$`\varepsilon_{\sigma+\omega}`$ より上の $`\mathrm{seg}(\sigma)`$、$`\mathrm{seg}(\upsilon_{\lambda+n})`$、$`\mathrm{seg}(\tau_1)`$、
  後のブロック）での H-RC。いくつもの区間にまたがる一般のピン（CL-FIN、LHPAR\*、有限集合の判定 T1 の一部に帰着
  済み）。$`y \ge \delta_j\cdot\omega`$ の点。$`\rho_{\Theta_A+\omega^2}`$ より上の $`R_2^C`$。$`T_\omega`$ より下のどの基の上でも、届く先はその基の上で
  走らせた形式的な届く先の再帰に従う（TAIL-GAP、今は証明済み、査読 1 回、[COVER-ja.md](COVER-ja.md) §5.1）。$`\nu`$ より下の Γ 型でないどのやり直しの添字でも、その値は
  OFF-V の閉じた形（$`\gamma = 0`$ で証明済み、今は $`\gamma \ge 1`$ も。[FANFREE-ja.md](FANFREE-ja.md) §3、§7.3）。未解決なのは臨界な添字の極限での届く先（[FANFREE-ja.md](FANFREE-ja.md) §7.3）。今は閉じた形はずれ $`\rho^\rho`$ まで届き、
  未解決なのは Klammer の臨界な類の数え上げの不動点の極限での届く先（[FANFREE-ja.md](FANFREE-ja.md) §10.3）。
- CL-FIN と LHPAR\*、だから初等再帰的な対応。今は CL-FIN と LHPAR\* の Cl\* の形は証明済み。LHPAR\* の鋭い形は書いた
  ままでは成り立たず、「初等再帰的」は概略だけ（[BREAK-ja.md](BREAK-ja.md) §4）。
- $`[\Lambda_\varepsilon, \Theta_1)`$ での $`c^+`$ の閉じた形。$`\Theta_P`$、$`\Theta_1`$、$`\Theta_A`$、$`\Lambda^*`$、$`\nu_P`$ の名前。$`D`$ がどこまで延びるか。
  $`\Lambda_\varepsilon`$ より上での主張の名前の半分。今は閉じた形がずれ $`\varepsilon_{\zeta_{\rho+1}+1}`$ まで成り立ち、$`\Theta_P`$ に名前が付き、主張は
  $`\rho_{\Lambda'+\omega^2}`$ まで成り立つ（[FANFREE-ja.md](FANFREE-ja.md) §10.4）。残り：$`(\Lambda', \Theta_1)`$ での閉じた形と、ほかの名前。今は閉じた形が
  $`e_\lambda \le \psi_{\Omega_2}(\Omega_2) + 1`$ のどのやり直しの点でも成り立ち、主張が $`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$ まで成り立つ。$`\Theta_1 = H(\theta)`$ は未解決の包の補題に帰着した（[VEBLEN-ja.md](VEBLEN-ja.md) §1）。今は閉じた形が
  $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$ で成り立ち、主張が $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ まで成り立つ。$`\Theta_1`$ と $`\Theta_A`$ の名前には未解決の補題 PAR-SAME だけが要る（[VEBLEN-ja.md](VEBLEN-ja.md) §8）。今は PAR-SAME が証明され、$`\Theta_1`$ と $`\Theta_A`$ に
  名前が付き、主張は $`\psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ まで成り立つ。$`\Lambda^*`$ と $`\nu_P`$ は下からの評価だけが証明済み（[THETA-ja.md](THETA-ja.md) §1）。今は $`\Lambda^*`$ と $`\nu_P`$ に名前が付き、主張は
  $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$ まで成り立つ（[THETA-ja.md](THETA-ja.md) §9.1）。さらに $`X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2)`$（$`G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})`$）まで（[SHIFT-ja.md](SHIFT-ja.md) §1）、FRAG のもとで $`X_5`$ まで（[SHIFT-ja.md](SHIFT-ja.md) §8.1）、そのあと $`X_8`$ まで（[SHIFT-ja.md](SHIFT-ja.md) §9.1）、$`X_9`$ まで（[SHIFT2-ja.md](SHIFT2-ja.md) §1.1）、$`X_{11}`$ まで（そこの §2.1）、$`X_{12}`$ まで（そこの §3.1）、$`X_{13}`$ まで（[SHIFT3-ja.md](SHIFT3-ja.md) §1.1）、$`X_{14}`$ まで（そこの §2.1）。
- INC1-S と INC1-nonups は今は証明済み（[BREAK-ja.md](BREAK-ja.md) §1）。RIGHT（どの $`\lt_2`$ の右端も $`\upsilon`$ の点）は今は $`R_2^S`$ で証明済み（[COVER-ja.md](COVER-ja.md) §5.1）で、$`\beta_0`$ より上の $`R_2^C`$ では未解決。
- $`C^*_3`$：最小のいちばん下の点（$`\nu_P`$ より上）、上半分、下半分、予想 CH（[BREAK-ja.md](BREAK-ja.md) §10）。最初の扇は $`T_\omega`$ より上で、未解決の仮定 $`FF_N`$ のもとでは到達不能基数が
  要る（[BREAK-ja.md](BREAK-ja.md) §7.4。今は $`m_F \ge \theta_0`$ と同じ、[FANFREE-ja.md](FANFREE-ja.md) §4）。もっと弱い未解決の仮定「$`\min\{m : m \le_1 x_F\}`$ が $`\ge \theta_0`$」のもとでも要る（この仮定は今は、右端に届く先の無い、扇の無い
  パターンについての下からの評価と同じ、[COVER-ja.md](COVER-ja.md) §5.3。そのいくつかの一様な段は証明済み、[COVER-ja.md](COVER-ja.md) §6.1。
  また $`m_F \gt \nu_C`$、[COVER-ja.md](COVER-ja.md) §6.4）。$`R_2^C`$ では鎖の底は
  特徴づけられ、$`c_0 \gt m_3 \ge \sup_n \varphi_n \gt f_0 \gt x_F`$。$`\varphi_n`$ は閉じた $`n`$ 扇の最小の頂点（[COVER-ja.md](COVER-ja.md) §1–2）。
