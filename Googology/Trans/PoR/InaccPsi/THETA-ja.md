[← Back](README-ja.md) | [English](THETA.md) | [Japanese](THETA-ja.md)

# $`R_2^+`$ の 13 回目と 14 回目：PAR-SAME、$`\nu_P`$ までの名前、$`X_3`$ までの主張、$`\upsilon`$ の不動点のための部品、(REP)、(HC)、ねじれた写し

このページは [VEBLEN-ja.md](VEBLEN-ja.md) の続きで、[SHIFT-ja.md](SHIFT-ja.md)、[SHIFT2-ja.md](SHIFT2-ja.md)、[SHIFT3-ja.md](SHIFT3-ja.md)、[SHIFT4-ja.md](SHIFT4-ja.md) がこの続き。状態の言葉は [README-ja.md](README-ja.md) の §3 と同じ：**証明済み**は、独立した査読者が、
致命的な点も止める点も無く証明済みと判定したもの。§1〜§7 は 13 回目（2026-10、4 つの論文）、§9 は 14 回目（2026-10、4 つの論文）。§8 には、README を短く保つためにそこから
移した 2 つの部分を置く：1〜12 回目のまとめと、$`R_2^S`$ と $`R_2^C`$ を比べた結果。
止める点のある命題は **未証明** に、査読者が目標の言い直しや注意にすぎないと判定した命題は **数えない** に書く。証明書は再生されたものだけを数える。
**移し替えとして証明済み** とは：査読済みの証明を、写像・基・添字の範囲を 1 つ変えて繰り返したもので、追加の事実が要る箇所を論文が
すべて挙げ、査読者がそのどれも認めたもの（[VEBLEN-ja.md](VEBLEN-ja.md) の §1 と §8 の L3 や H3 と同じ水準）。§1 の移し替えは §9.1 で全部書いた証明にした。

どの論文も 1 回ずつ査読された。だからここの結果は、回数を書いていなければ査読 1 回。どの論文も Wilken, JSL 72 (2007)、Carlson,
AML 38 (1999)、Wilken, AML 45 (2006) を使わず、Carlson 2009, p. 97 が予告する同値も使わない。Lean のファイルは足していない：1 つの論文（§1）が
名前を付けた点についての Lean の試験のファイルを leanman で確かめた（緑。査読者の再実行でも緑）が、項を比べるだけ（`#eval` だけで定理は無い）。
論文は入れ子の組の段を 1 つ小さく数えるので、ここでは番号を付け直した（論文の $`U^1`$ と $`u_n`$ は、ここでの $`U_2`$ と $`\upsilon^2_n`$）。

## 1. PAR-SAME、$`\Theta_1`$ と $`\Theta_A`$、$`\upsilon^*`$ までの主張

記号は [VEBLEN-ja.md](VEBLEN-ja.md) の §1 と §8 と同じ：$`A_\eta = \Omega_\omega + \theta\cdot\eta`$ として $`H(\eta) = \psi_{\Omega_1}(A_\eta)`$、$`C_\eta`$ は $`(A_\eta, H(\eta))`$ の InaccPsi の包、
$`D`$ は $`\eta \in C_\eta`$ となる $`\eta \lt \Omega_2`$ の集合、$`\upsilon^* = \sup H[D]`$（[PINS-ja.md](PINS-ja.md) §3）。$`T^\tau`$ は基 $`\tau`$ の上の Wilken の系
（Wilken 2007, APAL 145, 130–161）、$`\bar T^\tau`$ は Weiermann–Wilken（MLQ 57, 2011）の同時に定めた系。新しい記号：$`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$、
$`Z = \psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$、$`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$（だから $`G(0) = \theta`$）、$`D'`$ は $`\eta \in C_\eta`$ となる $`\eta \lt \Omega_\omega`$ の集合、
$`\iota'(\eta)`$ は $`D' \cap \eta`$ の順序型。$`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$。

- **FID と定理 PAR-SAME**（証明済み。2011 年の論文の Def 3.2、Cor 3.7(f)、Def 3.9、Def 4.7 と、Wilken 2007 の Def 3.28、Def 4.6、L.3.30 を、査読者が
  本文と照らし合わせた）。2011 年の論文の Cor 3.7(f) により、その Def 3.9 の順序同型 $`f^\tau`$ は恒等写像。だから $`T^\tau`$ と $`\bar T^\tau`$ は同じ集合で、
  変わるのは順序数を表す項だけ。PAR-SAME：どの $`\alpha \in T^\tau`$ でも、Wilken の系での項から読むパラメータ（Wilken 2007, Def 3.28）と、同時に定めた系での
  項から読むパラメータ（2011, Def 4.7）は等しい。これは 12 回目に足りなかった補題（[VEBLEN-ja.md](VEBLEN-ja.md) §8）。証明：2011 年の論文の Def 3.2 に沿った
  同時の帰納法。鍵となる段は、$`\Delta_1`$ の局所化の最初の元が $`\Delta_1`$ の部分項であること（Wilken 2007, Def 4.6）。（査読者：帰納法の中の 1 つの不等式には
  Wilken 2007, L.3.30 の引用が要る。）
- **系**（証明済み）。どの $`\sigma`$ でも $`T^\tau[\sigma] = \bar T^\tau[\sigma]`$。2 つの基の取り替え $`\pi_{\sigma,\tau}`$ は同じ写像。**READOFF**：$`\bar T^\tau`$ の式に書かれた
  パラメータが、その値のパラメータを抑える（だから前者が加法的主要数 $`\sigma`$ より下なら、後者もそう）。（査読者：READOFF は値が $`\tau`$ という自明な場合を
  挙げていない。）
- **定理 THETA1 と THETA-A**（証明済み、査読 2 回：12 回目の査読者が PAR-SAME 以外のすべての段を確かめ、この回の査読者が、PAR-SAME と READOFF で
  [VEBLEN-ja.md](VEBLEN-ja.md) §8 の止める点が求めた両方の向きが出ることを確かめた）。
  $`\Theta_1 = H(\theta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$ で $`\mathrm{lh}(H(\theta)) = H(\theta+\omega+1) + H(\theta+1)`$。$`\Theta_A = H(\varepsilon_{\theta+\omega}) = \psi_{\Omega_1}(\Omega_\omega + \varepsilon_{\theta+\omega})`$。
  だから $`R_2^C`$ での Wilken の主張は $`[0, H(\varepsilon_{\theta+\omega} + \omega^2))`$ で両方の半分とも成り立つ。12 回目の査読の 5 つの細かい点を反映した：
  $`E^{\Omega_1}`$ のパラメータは可算で極大な部分項の「中にある」；写像 $`\Psi^\#`$ は本来の定義域で読む；$`R_2^S`$ の引用を NU-CT に置き換える；NEST-CHAR は
  NU-CT の言い直しと付け直す（数えない）；$`\psi_{\Omega_2}(\Omega_2\cdot 2)`$ より下の包の補題は「もっともらしい」と付け直す。
- **TAU-BOUND、CONT₂、UPS\***（証明済み。[InaccPsi](../../../Notation/InaccPsi/README-ja.md) の事実と Lean の補題 `psi_one_iSup` と照らし合わせた）。$`\eta \in D'`$ と
  $`\tau \in C_\eta \cap \Omega_2`$ で $`\tau \lt \psi_{\Omega_2}(A_\eta)`$、そして $`\eta \in D`$ なら $`\psi_{\Omega_2}(A_\eta) \le Z`$。$`\psi_{\Omega_2}`$ は増加列で連続（CONT₂、補題 CONT の
  $`\Omega_2`$ 版）。$`\sup D = Z \notin D`$ で、

```math
\upsilon^* = \sup H[D] = \psi_{\Omega_1}(\Omega_\omega + \Omega_2) = H(\Omega_2).
```

- だから $`\upsilon^*`$ より下のどのやり直し $`\lambda`$ でも、指数は $`\tau_\lambda \lt Z \lt G(1)`$。前に分かっていたのは $`\upsilon^* \le \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ だけ。
- **GEN⁺**（移し替えとして証明済み）。[PINS-ja.md](PINS-ja.md) §3 の定理 GEN は $`D'`$ で成り立つ：どの $`\eta \in D'`$ でも $`H(\eta) = \upsilon_{1+\iota'(\eta)}`$。証明の中で
  $`\Omega_2`$ を名指す 1 か所は、$`\theta\cdot\eta \lt \Omega_\omega`$ しか要らない。
- **ずらした LOW-STEP の写像**（$`[\theta, Z)`$ では証明済みで、5 つの比べる場合をすべて査読者が 2011 年の論文の L.4.3 と L.4.4 と照らし合わせた。ほかの基では
  移し替えとして証明済み、SLOW$`_\zeta`$。査読者によると添字をずらしただけ）。値が $`[G(\zeta), G(\zeta+1))`$ にある InaccPsi の標準形から $`\bar T^{G(\zeta)}`$ への
  写像 $`E^{G(\zeta)}`$：狭義に増加し、どの節も定義域にあり、パラメータは $`G(\zeta)`$ より下の極大な部分項。**補題 S**（SUBST-ISO の移し替えとして証明済み）：
  非可算な基での代入。
- **定理 U\***（証明済み。基 $`\theta`$ での補題 S に依る。補題 S は今は全部証明した、§9.1。査読者：帰納法は R-CAP と同じく $`\lambda`$ について回すこと、1 つの上限 $`\kappa`$ は加法的主要数に
  選ぶこと）。$`\rho_\lambda \lt \upsilon^*`$ のどのやり直し $`\lambda`$ でも、形式的な届く先は $`\delta_\lambda + \upsilon_{\lambda+2}`$ より下。だから $`\Theta_\delta`$、$`\Theta_{d\omega}`$、$`\Lambda^*`$ は
  どれも $`\upsilon^*`$ 以上で、GEN の名前の外にある。
- **定理 F1：$`R_2^C`$ での $`[0, \upsilon^*)`$ の上の Wilken の主張**、両方の半分とも（証明済み。基 $`\theta`$ での補題 S という 1 つの移し替えに依る）。
  $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ より下のどの順序数も核にあり、つぶす関数の引数が $`I_\omega`$ より小さい InaccPsi の標準形の値。そして $`\nu_C \gt \upsilon^*`$。
  前は $`[0, \rho_{\Lambda_{\mathrm{fp}2}+\omega^2})`$。核の側は CORE-C$`^{d\omega}`$（[BREAK-ja.md](BREAK-ja.md) §4）から出る。$`\rho_{\Theta_{d\omega}} \ge \upsilon^*`$ だから。名前の側は補題 L と
  IS。これで [VEBLEN-ja.md](VEBLEN-ja.md) §1 の問いにも答えが出た：$`\nu_C`$ は $`\upsilon^*`$ より下ではない。
- **R-CAP と定理 F2**（移し替えとして証明済み：GEN⁺、SLOW$`_\zeta`$、基 $`G(\zeta)`$ での補題 S）。$`\eta_\lambda \lt \theta_2\cdot\omega^2`$ のどのやり直し $`\lambda`$ も
  $`\Lambda^*`$ より下。だから $`\Lambda^* \ge \iota'(\omega^{\theta_2+2})`$。[BREAK-ja.md](BREAK-ja.md) §2 と合わせて $`\nu_C \gt \nu_P \ge X_2`$、そして $`R_2^C`$ での Wilken の主張は
  $`[0, X_2)`$ で両方の半分とも成り立つ。
- **名前**（下からの評価は移し替えとして証明済み。等しいことは予想。**今は 4 つとも証明済み**、§9.1）。$`\rho_{\Lambda^*}`$ の名前はこの導き方から出てきて、行列から作った
  [REACHES-ja.md](REACHES-ja.md) §3 の前の予想と一致する。

| 点 | 予想する InaccPsi の名前 |
|---|---|
| $`\rho_{\Theta_\delta}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$ |
| $`\rho_{\Theta_{d\omega}}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2 + \omega^{\omega^{G+1}})`$、$`G = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$ |
| $`\rho_{\Lambda^*}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2})`$ |
| $`\nu_P`$ | $`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ |

- **数えない**：NEST-CHAR（上に書いたとおり NU-CT の言い直し）。（査読者：論文の 1 つの注意は、届く先の閉じた形が分かっている範囲を言い過ぎている。
  正確なのは $`e_\lambda \le \psi_{\Omega_2}(\Omega_2\cdot 2) + 1`$ と $`\Theta_A`$ だけで、その間は上下の評価だけ。）
- **未解決**（等しい側と $`\nu_P`$ は今は証明済み、§9.1）：名前の等しい側（基 $`G(\zeta)`$ でのずらした STEP、実現するものの符号、$`\delta_j\cdot\omega`$ と次のブロックのいちばん上の間の届く先の下からの評価が要る）；
  $`\nu_P`$ の正確な値；$`\nu_C`$ の InaccPsi による上からの評価（左端がやり直しの点である、正の $`\lt_2`$ の関係が 1 つ）。PAR-SAME と補題 S は試せなかった：
  Wilken の $`T^\tau`$ を実装したものが無い。

## 2. 素の符号：$`\upsilon`$ の不動点のための部品

記号は [VEBLEN-ja.md](VEBLEN-ja.md) の §2 と §9、そして [REACHES-ja.md](REACHES-ja.md) §1 の $`\upsilon`$ の上の Veblen の階層：$`V_1(\alpha) = \Xi_\alpha`$、$`V_{\nu+1}`$ は $`V_\nu`$ の不動点を
並べる。だから $`V_2(1) = \Phi_1`$。$`\Gamma^\upsilon_1`$ は $`V_\nu(1) = \nu`$ となる最小の $`\nu \ge 1`$。これは点 $`\Lambda_\Gamma = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1^2})`$ で、その名前は
[PINS-ja.md](PINS-ja.md) §3 で証明済み（論文はこの名前を未証明と呼ぶ）。

- **LEV、NO-HIGH、NO-HIGH-K**（証明済み。1 行ずつ確かめた）。$`\upsilon`$ の不動点 $`\zeta \lt \Gamma^\upsilon_1`$ はどれも、最大の段 $`\nu`$ を持つ $`V_\nu(1+\beta)`$ で、
  $`\nu, \beta \lt \zeta`$。$`\beta`$ の要る点より上で $`\zeta`$ より下の不動点は段が $`\nu`$ 以下で、段が $`\nu`$ ならもっと小さい $`\beta`$ を持つ。
- **補題 EXTRA**（証明済み。査読者：層 0 の段も同じ議論で済むが、1 文足りない）。[VEBLEN-ja.md](VEBLEN-ja.md) §9 の層の符号のどの段も、点より下の閉じた集合
  $`F`$ を余分に止めたまま成り立つ。新しい鎖は $`\max F`$ より上にある。
- **定理 MODULE-RED**（含意として証明済み）。ある上限 $`Z'`$ より下の $`\upsilon`$ のどの不動点にも、3 つの性質を持つ部品のブロックがあるとする：(MA) 決まった
  形（組が 1 つと、ふつうの内側の鎖が 1 つ）、(MB) ブロックは L1p の無いパターン、(MC) ブロックはもっと小さい不動点のブロックを宿す。すると
  符号は $`[\omega, Z')`$ で $`N(\gamma') \ll N(\gamma)`$ を満たし、$`\iota(\mathrm{CH}_2) \ge Z'`$。（査読者：論文は素の道全体が部品に帰着したと言うが、言い過ぎ。帰着したのは
  形 (MA) の部品で、次の種類の部品はこの形をしていない。）
- **定理 LADDER**（証明済み）。段ごとに 1 つのゆとりのブロック $`L_\nu(\beta)`$。いちばん上が $`c + x + r`$ のブロック $`J = L_2(0)`$ は $`\Phi_1`$ の部品で、conv が
  (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,1,0) について描くものとちょうど同じ（確かめ済み）。だから $`\iota(\mathrm{CH}_2) \ge V_{\omega^2}(1)`$。
- **定理 IDX-Γ**（証明済み）。内側の符号の部品：$`V_\nu(1+\beta)`$ のブロックは、組の中に $`N(\omega+\nu)`$ の鎖を持ち、そのいちばん上は $`\beta`$ とともに大きくなる。
  だから $`\omega \le \gamma' \lt \gamma \lt \Gamma^\upsilon_1`$ で $`N(\gamma') \ll N(\gamma)`$、そして素の符号で $`\iota(\mathrm{CH}_2) \ge \Gamma^\upsilon_1 = \Lambda_\Gamma`$（前は $`\Phi_1`$）。これはまだ、
  分かっている $`\iota(\mathrm{CH}_2) \gt \nu_C`$ よりはるかに下。進んだのは $`\iota(\mathrm{CH}_2) \ge \theta_0`$ へ向かう素の道の上だけ。
- **数えない**（査読者：定理ではなく注意）：「G. Wilken, Fundamental sequences based on localization（APAL 2025、arXiv 2410.15953）の基本列は 1 つの層の中に
  とどまる」。論文はその根拠に違う系を引いている（正しい箇所は Def 2.29 と Thm 2.28）。そして書かれたとおりでは正しくない：そこの Def 3.5 は、層の基を
  越える段を、入力として与えられた基の系から取る。
- **conv に沿った文法**：(G1) $`x`$ に相対的な内側の符号、概略だけ；(G2) $`\upsilon`$ の上のつぶす関数の階層、未解決（予想：$`\Theta_1`$ まで届く）；
  (G3) その先 $`\theta_0`$ までのすべて、未解決。
- **未証明**：$`\iota(\mathrm{CH}_2) \ge \theta_0`$。論文もそう言う。隙間：$`\Gamma^\upsilon_1`$（$`\zeta`$ が $`V_\zeta`$ の値域に入る所）から $`\theta_0`$ までの $`\upsilon`$ の不動点のための部品。
  次の種類の部品は (MA) に合わない：組より上の 2 つ目の内側の鎖、$`x`$ を含む内側の和、conv の次のブロック $`c \le_1 c + y`$ と $`c \le_1 c\cdot 2`$。だから
  まず MODULE-RED そのものを広げる必要がある。

## 3. $`\Phi_3`$ の形：(REP) の証明と、$`t = 2`$ の階段

記号は [VEBLEN-ja.md](VEBLEN-ja.md) の §3 と §10 と同じ。定理は $`\Phi_3`$ の文章での定義とプログラム `por/phi3def2.py` についてのもので、すべて $`R_2^C`$ の中。

- **PRES-IN、PRES、定理 REP**（証明済み。査読者はプログラムと 1 行ずつ照らし合わせ、使われないコードの一覧と、使われる 5 つの同一性の判定を
  確かめた）。$`A[0]`$ と $`A[1]`$ の組についての 2 つの条件：(J) 子の $`y`$ は親の $`y + 1`$ 以下；(N) $`z = 1`$ の列は、1 段上に $`z = 1`$ の子を持たない。これらは
  どの $`A[j]`$ にも引き継がれ、標本の 3,166 個の行列はすべて満たす（計算で判定）。このもとで、プログラムの段の列の部分は一度も走らず、評価される
  同一性の判定は 5 つだけで、どれも位置による判定と同じ。だから実行は、オブジェクトの持ち方にも呼び出しの順にもよらず、閉包は順によらず、
  プログラムは文章での定義と同じ：(REP) が成り立つ。だから SYM、SYM-P、SYM-R と、[FANFREE-ja.md](FANFREE-ja.md) §10.1 以来の記号的な結果はどれも (REP) 無しで
  成り立つ。[VEBLEN-ja.md](VEBLEN-ja.md) §10 の 1,862 個の行列は、条件無しで証明済みになった。（査読者：補助の補題 F1′ は $`y = 1`$ のオブジェクトでだけ成り立ち、
  使うのもそこだけ。REP はこれに依らない。）**見つかったこと**（未解決、SRO より上だけ）：プログラムの 1 つの枝では、記録が閉包から漏れうる。
  SRO より下ではそこに来ない。
- **L-STAIR と REL-OPQ**（証明済み。REL-OPQ には、1 つの場合分けが項全体によらない理由をもう 1 文書く必要がある）。最初の写しの段は階段を 1 段下げる。
  中身を見ない印を置いた項の上で、変えていないプログラムを走らせて終われば、許されるどの代入でもその結果が出る。
- **定理 STAIR-V**（有限の基の確かめ B0〜B6 のもとで証明済み。B0〜B6 は 96 + 29 個の行列のすべてで通り、査読者も走らせ直した）。類 STAIR
  （$`t = 2`$、鎖の始まり $`C`$ が悪い根の子、鎖の尾が根の最後の子）で、どの $`n \ge 4`$ でも conv$`(A[n])`$ を明示的に書く。
- **TRANSFER と STAIR-FS**（TRANSFER は査読者の直しのあとで証明済み：段 $`n+1`$ の相対的な節はどれも $`y \ge 6`$、尾の節はどれも $`y \le 3`$ なので、
  最後の区間は変わらない）。ROOT の 96 個と III の 29 個の行列で、どの $`n`$ でも FS⁺。
- **数え上げ**（$`1{,}987 = 1{,}862 + 125`$ を査読者が確かめた）：

| 類 | 行列 | すべての $`n`$ で証明済み | LOW のもとで | 小さい $`n`$ で確かめた条件のもとで | $`t = 2`$、小さい $`n`$ で確かめた形のもとで | 未解決 |
|---|---|---|---|---|---|---|
| I | 581 | 381 | 2 | 0 | 0 | 198 |
| SUM | 603 | 488 | 0 | 7 | 0 | 108 |
| ROOT | 635 | 587 | 0 | 0 | 0 | 48 |
| III | 1,347 | 531 | 0 | 0 | 24 | 792 |
| 計 | 3,166 | 1,987（前は (REP) のもとで 1,862） | 2 | 7 | 24 | 1,146 |

- **未解決**：SRO より下の UNIF-FS。証明されていない 1,179 個の行列：$`t = 0`$ が 462 個（M1 が 258、M2 が 139、M3〜M5 が 65。[VEBLEN-ja.md](VEBLEN-ja.md) §10 と
  同じ）；$`t = 2`$ が 335 個（III の 24 個はいちばん上の鎖の頭が動き、2 つのモードを持つ $`\iota`$ が要る；III の 136 個と ROOT の 31 個は $`C`$ が悪い根の子より深いか、
  導き方が途中で失敗する；I と SUM の 144 個は核の持ち上げが要る）；$`t = 1`$ が 382 個。M1 は手を付けていない：走りの長さが 2 か所にある入れ子の
  ブロックについての定理が要る。

## 4. $`\nu_C = \nu_S`$：(HC) の証明と、ねじれた残り

記号は [VEBLEN-ja.md](VEBLEN-ja.md) §11 と同じ：$`u_m = \upsilon^2_m`$、$`x = x_2`$、$`\nu = \nu_C`$、$`P^*`$ は $`x, \nu \in P^*`$ の同型最小な集合、$`\tilde x = u_m`$ は $`x`$ の下向きの写し、
$`g = u_m^\#`$。

- **U-CHAIN と定理 HC**（証明済み。Carlson 2009 の Def 2.3 と 2.6 と照らし合わせた）。$`J`$ が同型最小で $`\nu \in J`$ なら、$`N \ge n^*`$ のどれでも
  $`J \cup \{u_{n^*}, \ldots, u_N\}`$ は同型最小。ここで $`u_{n^*}`$ は $`\max(J \cap x)`$ より上の $`U_2`$ の最初の点。これらの点は $`[x, x^\#)`$ を何も変えないが、写し $`\tilde x = u_m`$ を
  遺伝的なパラメータのどんな有限集合よりも上に押し上げる。だから (HC) が成り立ち、[VEBLEN-ja.md](VEBLEN-ja.md) §11 の COPY-EQ、LOC#、ET-TF、GHOST-TR
  （査読者の直した形）は仮定無しで成り立つ。
- **RED-TF**（証明済み。[VEBLEN-ja.md](VEBLEN-ja.md) §11 の止める点の 2 つの穴をどちらも埋める）。低い点（$`g`$ より下）は、Cantor 標準形の後ろの部分に $`T_m`$ を
  当てて送る。上の部分には、像が $`(x^\#, \nu)`$ にある写し $`\Psi_0`$ が 1 つ要る。残る条件は
  (CUT′)：$`a \le_1 B + w`$ ⇔ $`\Psi_0(a) \le_1 \Psi_0(B) + T_m(w)`$ だけ。ほかの原子はどれも自動的に決まる。
- **ISO-EXT、LOW-ISO、UNTWIST、GHOST-TW**（証明済み。査読者：UNTWIST の 1 つの段は行き先の集合が閉じていると仮定する。これは UP-EX から短い議論で
  出るが、書かれていない）。広げた同型最小な基の上の Carlson の上向きの規則は、低い点をどれも動かさない。それは $`w \lt u_m`$ のすべて、高い尾のすべて、
  そしてどの $`w`$ でも「⇐」の向きで (CUT′) を与える。だから幽霊には **ねじれた三つ組** が要る：$`\mathrm{lh}(a) = B + r`$、$`u_m \le w \le r \lt u_m^\#`$ となる上の点 $`a`$ で、
  正確な上向きの写しが届く先の端を $`x`$ に動かさず $`u_m`$ のままにするもの。
- **TW-0**（[FANFREE-ja.md](FANFREE-ja.md) §10.3 の定理 KV のもとで証明済み）。添字 $`\iota`$ が $`\upsilon`$ の不動点でないやり直しでは、ねじれを添字に入れられる：
  $`l' = T_m(\mathrm{logend}(\iota))`$ として $`\iota' = \omega^{x^\# + l' + 1} + \omega^{l'}`$。これは $`x`$ より上の $`K`$ の $`\omega`$ 番目の点より下にあり、その点は $`\nu`$ より下。だから
  [VEBLEN-ja.md](VEBLEN-ja.md) §11 の例 TW は $`\nu`$ より下で実現される。（査読者：$`\max(P^* \cap \nu)`$ より上にそのような点を求めた注意は、これでは片付かない。
  それを要するものは無い。）
- **ZONE-RED と LH-LAMBDA**（条件付きの補題として証明済み。ZONE-RED は挙げた性質に無い事実を 1 つ使うが、それは挙げた性質から出る）。
  上のことはどれも、性質 (Z1)〜(Z5) を持つ区域の系なら何でも成り立つ。定理 KV は $`u^\#`$ で終わる区域を与える。届く先は、$`u`$ より上の $`k`$ の不動点の
  最小の極限 $`\lambda_u`$ より下にとどまる。
- **未証明**：(TWIST\*)、上の配置全体のねじれた写し。示されたのは、上の部分が $`\{\rho_\iota, \delta_\iota\}`$ で $`\iota`$ が $`\upsilon`$ の不動点でないときだけ。
  $`\mathrm{Fix}_1 \setminus K`$ のやり直し、$`K`$ の点、いくつかのブロックを同時に、点 $`u_{m+j}`$、区域 C では足りない。(R2) には $`[u^\#, \lambda_u)`$ での (PROF) と区域 C が要る。
  $`\nu_C = \nu_S`$ も $`\nu_C \lt \nu_S`$ も証明されておらず、最初の食い違いも見つかっていない。（査読者：論文が 1 か所で「同値」と書くのは、(TWIST\*) から ET が
  出ることしか示していない。）

## 5. 13 回目のあとの状況

14〜35 回目でこの状況は変わった。§9.5、[SHIFT-ja.md](SHIFT-ja.md) の §5、§8.5、§9.5、[SHIFT2-ja.md](SHIFT2-ja.md) §1.5、§2.5、§3.5、[SHIFT3-ja.md](SHIFT3-ja.md) §1.5、§2.5、[SHIFT4-ja.md](SHIFT4-ja.md) §1.5、§2.5、[SHIFT5-ja.md](SHIFT5-ja.md) §1.4、§2.4 と [SHIFT6-ja.md](SHIFT6-ja.md) §1.4、§2.4、§3.4、[SHIFT7-ja.md](SHIFT7-ja.md) §1.4、§2.4、§3.4、[SHIFT8-ja.md](SHIFT8-ja.md) §1.4、§2.4、[SHIFT9-ja.md](SHIFT9-ja.md) §1.4 を見よ。


- $`R_2^C`$ での Wilken の主張：両方の半分が $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ として $`[0, \upsilon^*)`$ で成り立ち（1 つの移し替えに依る）、
  $`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ として $`[0, X_2)`$ でも成り立つ（移し替えとして証明済み）。$`\Theta_1 = H(\theta)`$ と $`\Theta_A = H(\varepsilon_{\theta+\omega})`$（査読 2 回）。$`\nu_C \gt \nu_P \ge X_2`$。
- $`\theta_0`$ より下の下界の計画：SRO より下の段は、標本の 3,166 個のうち 1,987 個の行列で、プログラムについての条件無しに、すべての $`n`$ で証明済み（§3）。
  素の符号は $`[\omega, \Lambda_\Gamma)`$ で順序が付き、だから素の符号で $`\iota(\mathrm{CH}_2) \ge \Lambda_\Gamma`$。残りは形 (MA) の部品に帰着した（§2）。
- 最初の到達不能基数：$`H_m`$ は未解決。$`\iota(\mathrm{CH}_2) \ge \theta_0`$ から出る。
- 上からの評価：どの $`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ にも、InaccPsi による評価は証明されていない。
- $`\nu_C = \nu_S`$：(HC) が成り立ち、帰着は直され、ねじれた三つ組以外はすべて対応が付く（§4）。残り：(TWIST\*)、(PROF)、区域 C。

## 6. 13 回目の確認

どの実行も 60 秒以内。どれも証明ではない。証明書は再生されたものだけを数える。

- §1。$`[\theta, Z)`$ での $`E^\theta`$：2,500 個の項、806,640 組で、順序・定義域・パラメータの失敗は 0。わざと壊したものは失敗する（18,222 と 367 の食い違い）。
  基 $`\theta`$、$`G(1)`$、$`G(\omega)`$ での一般のずらした写像：502,264 組で失敗 0。壊したものは失敗する。$`\tau \in C_\eta`$ の組 $`(\tau, \eta)`$ 12,883 個はすべて $`\psi_{\Omega_2}(A_\eta) \le Z`$ より下。
  名前を付けた 11 個の点は標準形で狭義に増加する（Python と Lean の試験のファイル、緑）。査読者：新しい種での再実行で失敗 0。自分の生成器で：
  1,000 個の項と 280,920 組の $`E^\theta`$ で失敗 0。$`Z`$ より下のランダムな標準形 400 個はすべて $`\zeta_8`$ より下、$`\upsilon^*`$ より下の可算なランダムな標準形 474 個は
  すべて $`H(\zeta_8)`$ より下（$`\zeta_0 = 0`$、$`\zeta_{n+1} = \psi_{\Omega_2}(A_{\zeta_n})`$）。これは $`\sup_n \zeta_n = Z`$ を支える。$`\Omega_2`$ より上での TAU-BOUND：3,262 組で失敗 0。
  PAR-SAME と補題 S は試していない（$`T^\tau`$ を実装したものが無い）。
- §2。15 個の部品のパターン（14 個が新しい。SRO は新しくない）は、パターンで、RF で、扇が無く、L1p が無い。予想した向きの証明書 19 個中 19 個が
  見つかり再生された。逆向きの探索 7 回では何も見つからない。査読者：再実行は同じ出力。論文の 6 つの conv の描画は一致。自分の逆向きの探索
  10 回では何も見つからず（どれも約 45 秒で止めた）、自分の順向きの 4 組は見つかって再生された。探索が浅いので、弱い証拠。
- §3。15,830 回の組み立てで PRES の違反は 0。計測した実行は、ちょうど 5 つの同一性の判定を評価する。$`n = 2, \ldots, 9`$ での段の構造と、段 6〜9 での
  移した解。著者自身の道具の誤り（III の番号付けでの階段の定数の誤り）と、L-STAIR の足りない仮定（増えない子）が見つかって直され、125 個を
  すべて走らせ直した。査読者：16,632 回の組み立てで違反 0。B0〜B6 を走らせ直して同じ結果。変異の試しで、確かめるものが誤った値をはねることを確認。
  ROOT で $`n = 10, \ldots, 18`$、III で $`n = 10, \ldots, 13`$ の段で失敗 0。
- §4。論文は何も走らせていない。査読者の、Cantor 標準形の上の RED-TF の写像の小さな模型：14,400 組で失敗 0。

## 7. 未解決

14〜35 回目でこのリストは変わった。今のリストは [SHIFT9-ja.md](SHIFT9-ja.md) §1.6。


- 最初の到達不能基数：$`H_m`$（$`\iota(\mathrm{CH}_2) \ge \theta_0`$ で足りる。それには、MODULE-RED を形 (MA) の外に広げて、$`\Lambda_\Gamma`$ から $`\theta_0`$ までの $`\upsilon`$ の
  不動点のための部品を作るか、文法 (G1)〜(G3) が要る）；§3 の未解決の 1,179 個の行列での SRO より下の UNIF-FS；$`\iota(A_n) \ge |\tau_n|`$。
- 上からの評価：$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$、または $`\nu_C`$（やり直しの点での正の $`\lt_2`$ の関係が 1 つ）の、どんな InaccPsi による評価も；STEP-CH；
  REL-SHARP；(HQ)。
- $`\upsilon^*`$ より先の名前：§1 の表の等しい側（基 $`G(\zeta)`$ でのずらした STEP、実現するものの符号、$`\delta_j\cdot\omega`$ と次のブロックのいちばん上の間の届く先の
  下からの評価）；$`\nu_P`$ の正確な値；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ（[VEBLEN-ja.md](VEBLEN-ja.md) §1 の包の補題）。
- $`\nu_C = \nu_S`$：§4 で足りない場合の (TWIST\*)、(PROF)、区域 C；$`k`$ の不動点の極限での届く先。
- [COVER-ja.md](COVER-ja.md) §9 の残り。

## 8. README から移したもの

### 8.1 1〜12 回目のまとめ

$`\upsilon_{\omega\cdot\omega}`$ より下では、主張は $`R_2^C`$ でも $`R_2^S`$ でも成り立つ：$`\upsilon_{\omega\cdot\omega}`$ 未満の
どの順序数も核に入り、しかも、つぶす引数がすべて $`I_\omega`$ 未満の InaccPsi の標準形の可算な値である（[README-ja.md](README-ja.md) §3 の定理 LOW）。
Wilken の点には正確な名前がある：$`\eta \lt \Gamma_0`$ で $`\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$（定理 T、§4）。
いまは $`\iota \mapsto \upsilon_\iota`$ の最初の不動点 $`\Xi_1`$ 未満のどの $`\eta`$ でも（定理 T+）。補題 FRAG は証明済みになった。
これら 2026-10 の結果（FRAG、FRAG2、やり直しのブロック、T+）は 2 ページ目 [RESTARTS-ja.md](RESTARTS-ja.md) にある。
3 ページ目 [REACHES-ja.md](REACHES-ja.md) に最新の結果がある：$`\Lambda_\varepsilon`$ までのすべてのやり直しの点の正確な届く先
（一部は査読 2 回）、名前 $`\Xi_\alpha = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1}\cdot\alpha)`$（査読 2 回）、これにより $`R_2^C`$ で
$`\Phi_1`$ まで主張が成り立つこと、骨組み型の範囲全体での $`R_2^S`$ の構造、骨組みが終わる所、長さ 3 の最小の鎖。
4 ページ目 [PINS-ja.md](PINS-ja.md) には次の回の結果がある：$`R_1^+`$ の相対化したパターン（Wilken が予告した相対化した核。
「初等再帰的」以外は作り直した）、$`\Theta_A`$ までの正確な届く先、すべての $`\upsilon`$ の点の名前
$`\upsilon_{1+\iota(\eta)} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$（定理 GEN）、これにより $`R_2^C`$ で $`\Lambda_\varepsilon`$ まで主張が成り立つこと、
長さ 3 の鎖のいちばん下の形。補題 LEFT に見つかった穴も記録した。5 ページ目 [BREAK-ja.md](BREAK-ja.md) には最新の 2 回の結果が
ある：INC1、NOBAD、補題 LEFT を仮定なしで証明したこと、$`R_2^S`$ の骨組み型でない最初の点を正確に求めたこと、$`R_2^C`$ のそれは
余分な組が 1 つある場合を除けば同じ点であること、入れ子の組のどの段でも最初のブロックの形、段の極限はどの組にも
入らないこと、長さ 3 の鎖は極限が左端である扇だということ（だから形 C3′′ は偽）、閉包 $`C_\tau(z)`$ が有限であること、
$`R_2^C`$ の核が $`\nu_C \gt \nu_P`$ まで延びたこと。その §7 は 3 回目の結果：入れ子の組の段の極限 $`T_\omega`$ より下では、どの段の
どのブロックも最初のブロックと同じ形（定理 SH）、どの扇の頂点も $`T_\omega`$ より上（査読 2 回）、最小の扇の後の元はちょうど 2 つで、
$`R_2^C`$ では開いている、$`\nu_C = \nu_S`$ かどうかは $`R_2^S`$ だけの問い、$`\nu`$ の名前と隙間の間の基の付け替えは添字の命題 $`o_2 = \omega`$ と
ほか 2 つに帰着。その §8 は 4 回目：$`R_2^C`$ では、入れ子の組のどの段も左端より下にちょうど $`\omega`$ 個の点を持つ（どの $`k`$ でも
$`o_k = \omega`$、定理 O$`^C`$、査読 1 回。被覆に対する Carlson の最小性による）。だから NU-NAME の形の部分が $`R_2^C`$ で成り立つ。$`R_2^S`$ では
$`o_2 = \omega`$、$`\nu_P`$ より上の NOLIM、$`\nu_C = \nu_S`$ は未解決のまま。$`\nu_C = \nu_S`$ から今は $`o_2 = \omega`$ が出て、NOLIM は隙間ごとの 1 つの
命題に帰着した。6 ページ目 [COVER-ja.md](COVER-ja.md) は 5 回目で、どれも同じ最小性による（どれも査読 1 回）：$`R_2^C`$ では、
核の点が長さ 3 の鎖の底であるのは、右端の無限の $`\le_1`$ 鎖を持つときちょうど（定理 CP3）。最小の扇は順序型以外は記述でき、
NOLIM が成り立つ。$`R_2^S`$ では、$`\nu_C = \nu_S`$ はそこでの NOLIM と $`o_2 = \omega`$ と同じで、$`o_k = \omega`$ は Carlson の最小性の
$`R_2^S`$ の形と 1 つの止める命題に帰着した。その §5 は 6 回目（どれも査読 1 回）：$`R_2^S`$ の段 0 の記述はどの可算順序数でも
成り立つ（だから SKEL⁺、SKEL$`^\omega`$、$`R_2^S`$ の RIGHT は証明済みで、それらを使う結果、$`R_2^C`$ の NOLIM もその 1 つ、は概略から証明の
段階に上がる）。$`R_2^C`$ の最小の扇の順序型は $`\omega^2`$。その最小の $`\le_1`$ の前の元 $`m_F`$ が $`\ge \theta_0`$ か（そうなら扇に到達不能基数が要る）は、
右端に届く先の無い、扇の無いパターンについての下からの評価とちょうど同じ。Carlson の最小性の $`R_2^S`$ の形は $`\beta_0`$ まで成り立つ。
その §6 は 7 回目（どれも査読 1 回）：パターンの間の比較の計算で、$`\theta_0`$ のいちばん上の段（SRO での）といくつかの一様な段の族を
証明したが、すべてではないので、最初の扇に到達不能基数が要るかは未解決のまま。$`m_F \gt \nu_C`$。最小の扇や最小の鎖の上からの
評価には $`\lt_2`$ の組 1 つともう 1 点があれば足りるが、InaccPsi の項による評価は証明されておらず、提案された 2 つの帰着は目標の
言い換えにすぎない。$`\nu_C = \nu_S`$ は $`R_2^S`$ と $`R_2^C`$ が共有する構造の中の 1 つの $`\Sigma_2`$ の命題で、最初のブロックで証明済みの、段 2 の
区間についての条件から出る。最小の扇の名前は、基 $`I_0`$ で予想した（類推だけ）。7 ページ目 [FANFREE-ja.md](FANFREE-ja.md) は 8 回目（どれも査読 1 回）：下界の標本の
決まらない 26 個の極限の跳びはすべて証明済み。$`m_F`$ は組の列の 1 本の具体的な列の点の極限なので、最初の扇に到達不能基数が要るのは、
その列のどれかの点が $`\theta_0`$ 以上のときちょうど（$`FF_N`$ も同じ仮定）。$`m_F`$ の上からの評価はこの 1 本の列の評価。$`\varepsilon_0`$ より下の
添字の族の上に行列を使わない写像を作ったが、その順序の証明には穴がある。段 2 の各区間の最初の部分では、区間の間でやり直しの点の
届く先が対応する（概略だけ）。同じページに 9 回目（どれも査読 1 回）もある：SRO より下の下界の計画の段は、標本の 3,166 個の行列のうち
459 個で、すべての $`n`$ で証明済み（以前の穴 IDX-ADD を含む）。残りは 4 つの未解決の部分に分かれる。素の符号は $`\varphi_\omega(0)`$ まで順序が
証明され、配置 L1p の無い扇の無いパターンはどれも $`\mathrm{CH}_2`$ の点より下にある。だから $`\theta_0`$ より下のすべての項をそのようなパターンに
写す写像があれば、最初の扇に到達不能基数が要ることが出る。$`\nu_C`$ より下のどのやり直しの点の届く先も、「臨界な」添字の極限を除いて
分かり、区間の条件 SC はそのような最初の極限まで証明済みだが、$`\nu_C = \nu_S`$ は未解決のまま。$`\mathrm{CH}_2`$ の点の InaccPsi による上からの
評価は証明されておらず、そのような評価は、ちょうど $`\nu_C`$ より上の 1 点での 3 つの関係。同じページに 10 回目もある（どれも査読 1 回）：
$`R_2^C`$ で主張は $`\rho_{\Lambda'+\omega^2}`$ まで成り立ち、そこのどのやり直しの点の届く先も閉じた形で
書け、$`\Theta_P`$ に名前が付いた。SRO より下の段は標本の 3,166 個のうち 874 個ですべての $`n`$ で証明済み。素の符号は Bachmann–Howard 順序数まで
順序が証明された。$`\nu_C`$ より下の届く先はずれ $`\rho^\rho`$ まで分かり（$`\upsilon`$ の上の Klammer の階層）、SC は各区間のより大きい部分で成り立つ。
しかし SC への帰着はいつも長いやり直しの点を要り、そこでは届く先のどんな閉じた形も使えないので、$`\nu_C = \nu_S`$ は未解決のまま。8 ページ目 [VEBLEN-ja.md](VEBLEN-ja.md) に 11 回目がある（どれも査読 1 回）：
Wilken の包の段を Veblen 関数と $`\Gamma`$ に合わせたので、$`R_2^C`$ で主張は $`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$ まで成り立つ。
$`\nu_C`$ より下では、やり直しの点の Klammer の形がその InaccPsi の名前から読める。$`\Theta_1 = H(\theta)`$ は未解決の包の補題 1 つに帰着した。SRO より下の段は
標本の 3,166 個のうち 1,442 個ですべての $`n`$ で証明済み。素の符号は $`\upsilon_1`$ より下のすべての添字と 1 段の参照で順序が証明され、だから
$`\iota(\mathrm{CH}_2) \ge \upsilon_2\cdot\upsilon_1`$。$`\nu_C = \nu_S`$ については、Carlson の 2-反映が正確な写しを与え、写しより上のどの拡張も合わせられるが、2 つの局所的な
命題への帰着には止める穴があるので、$`\nu_C = \nu_S`$ は未解決のまま。同じページに 12 回目もある（どれも査読 1 回）：主張は Γ の 2 つ目の
不動点までのずれで $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ まで成り立つ。$`\Theta_1`$ と $`\Theta_A`$ の名前には、パラメータについての短い未解決の補題 PAR-SAME が 1 つだけ要る
（それが無いと証明に止める穴がある）。SRO より下の段は標本の 3,166 個のうち 1,862 個で、プログラムの確かめた性質 (REP) のもとで、すべての $`n`$ で
証明済み。素の符号は $`\Phi_1`$ より下のすべての添字で順序が証明され、だから $`\iota(\mathrm{CH}_2) \ge \Phi_1`$。$`\nu_C = \nu_S`$ については、写しが正確に分かる区域で、正した
帰着が働かないので、未解決のまま。$`C^*_3`$ は $`\omega_1^{CK}`$ より下（Carlson 2009,
Thm 15.2）だが、InaccPsi の項による上からの評価も名前もまだ無い。12 回目のあとでは、$`R_2^C`$ では $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ より上（核の側は $`\nu_C`$ まで証明済み）、$`R_2^S`$ では
$`\upsilon_{\omega^3}`$ より上で、どちらの半分も未解決だった。13 回目はこのページの §1〜§7。

### 8.2 $`R_2^S`$ と $`R_2^C`$

この部分の結果はどれも 2026-10 のもの。2 つの構造で、ある関係 $`\alpha \le_i \beta`$ が食い違う最小の段 $`\beta`$ を
$`\beta_0`$ とする（等しければ $`\beta_0 = \infty`$）。$`\beta \ge \kappa`$ のすべてで $`\kappa \le_1^X \beta`$ となる最小の $`\kappa`$ を $`\kappa_X`$ とする。

- **補題 STAGE。** $`\beta`$ より下のすべての組で 2 つの構造が一致するなら、$`\alpha \le_1^S \beta \Rightarrow \alpha \le_1^C \beta`$。
  さらに $`\beta`$ への $`\le_1`$ も一致するなら、$`\alpha \le_2^S \beta \Rightarrow \alpha \le_2^C \beta`$。道具：有限集合による判定
  （[README-ja.md](README-ja.md) §3 の T1）、定理 EQ の先頭の項への置き換え、Wilken 2021 の Lemma 1.7(2) の $`R_2^+`$ 版、$`\Pi_2`$ 文の移し。
- **系 FIRST。** 右端が $`\beta_0`$ 以下の $`R_2^S`$ の関係（$`\le_1`$ でも $`\le_2`$ でも）は、どれも $`R_2^C`$ で成り立つ
  （「右端が $`\beta_0`$ の $`\le_2`$」の場合は 2 本目の論文で足した。2026-10、査読 1 回）。$`\beta_0`$ での食い違いは、$`R_2^C`$ の余分な関係。だから $`R_2^S = R_2^C`$ は、一致する段のすべてで逆向き
  （$`C \Rightarrow S`$）が成り立つことと同値。また $`\beta_0 \ge \upsilon_{\omega^3}`$（FRAG を使う。
  FRAG は証明済みになった。いまは $`\beta_0 \ge \Lambda_\varepsilon`$ かつ $`\beta_0 \ge \rho_{\Theta_P}`$、[REACHES-ja.md](REACHES-ja.md) §1–2。さらに
  $`\beta_0 \ge \rho_{\Theta_A}`$、[PINS-ja.md](PINS-ja.md) §2。さらに $`\beta_0 \ge \rho_{\Theta_A+\omega^2}`$、[BREAK-ja.md](BREAK-ja.md) §4。いまは $`\beta_0 \ge \nu_C \gt \nu_P`$、§2）、
  $`\beta_0`$ は可算か $`\infty`$。
- **定理 LOC**（2026-10、査読 1 回。[BREAK-ja.md](BREAK-ja.md) §7.3）。$`\beta_0`$ は、Carlson の被覆の条件を $`R_2^S`$ の中で評価したものが
  $`R_2^S`$ と違う最小の段。だから $`\nu_C = \nu_S`$ かどうか（「幽霊」が無いか）は $`R_2^S`$ だけの問い。今は、$`\nu_C = \nu_S`$ から
  $`R_2^S`$ での $`o_2 = \omega`$ が出て、NOLIM を仮定すれば両者は同じ（[BREAK-ja.md](BREAK-ja.md) §8.1、査読 1 回）。今は、$`\nu_C = \nu_S`$ は $`R_2^S`$ で NOLIM と $`o_2 = \omega`$ が
  成り立つことと同じ（GHOST-EQ）で、NOLIM は $`R_2^C`$ で成り立つ（定理 NOLIM$`^C`$）（[COVER-ja.md](COVER-ja.md) の §3 と §5.1、査読 1 回）。今は、$`\nu_C = \nu_S`$ ⇔
  $`x_2 \lt_2^S \nu_C`$。これは $`\nu_C`$ より下の共通の構造の中の 1 つの $`\Sigma_2`$ の命題（定理 EQ、[COVER-ja.md](COVER-ja.md) §6.3、査読 1 回）。その元の条件 SC は、段 2 の各区間の
  最初の部分で成り立つ（概略だけ、[FANFREE-ja.md](FANFREE-ja.md) §3）。今は、臨界な添字の最初の極限より下の、より大きい部分で証明済み（[FANFREE-ja.md](FANFREE-ja.md) §7.3）。さらに大きい部分でも
  証明済み（[FANFREE-ja.md](FANFREE-ja.md) §10.3）。しかし SC への帰着は、届く先のどんな閉じた形も使えない長いやり直しの点での SC をいつも要る（NEED-C、同じ所）。
  $`\Sigma_2`$ の命題を直接扱うと（査読 1 回、[VEBLEN-ja.md](VEBLEN-ja.md) §4）：isominimal な集合の上では Carlson の 2-反映が正確な写しを与え、写しより上のどの
  拡張も、長いやり直しの点を含めて合わせられる（TOP）。残るのは、写しより下の有限集合を止めたままの、局所的な基の取り替えと平行移動（その
  集合無しの 2 つへの論文の帰着には止める穴がある）。その集合を止めると（査読 1 回、[VEBLEN-ja.md](VEBLEN-ja.md) §11）：未解決の条件 (HC) のもとで、
  下向きの写しは SC の基の取り替えによる写しで、局所的な部分が成り立つ。しかしそこでは平行移動が成り立たないので、この帰着は働かない。
  残り：(HC)、その区域より先の局所的な部分、「ねじれた」上向きの規則。13 回目（§4）で (HC) が証明され、帰着が直され（RED-TF）、残りは
  上の配置全体のねじれた写し (TWIST\*)、(PROF)、区域 C になった。
- **補題 UPG。** 一致する段では、$`\alpha`$ 未満のどの $`\gamma`$ も $`R_2^C`$ で $`\alpha`$ の isominimal な部分集合に入るなら、
  $`\alpha \le_1^C \beta \Rightarrow \alpha \le_1^S \beta`$（$`\alpha = \kappa_C`$ と $`\alpha = \upsilon_{\omega\cdot\omega}`$ で成り立つ）。
- **KAPPA と CORE-EQ。** $`\kappa_C \le \beta_0 \Rightarrow \kappa_C \le \kappa_S`$、$`\kappa_S \le \beta_0 \Rightarrow \kappa_S \le \kappa_C`$。だから
  $`\max(\kappa_S, \kappa_C) \le \beta_0`$（AGR と呼ぶ）なら $`\mathrm{Core}(R_2^S) = \mathrm{Core}(R_2^C)`$。$`R_2^C`$ での主張と AGR から、
  $`R_2^S`$ での主張が出る。
- **一致する段での逆向き $`C \Rightarrow S`$**（2026-10、査読 1 回）。$`\alpha`$ 未満のどの $`\gamma`$ も $`\alpha`$ の isominimal な
  部分集合に入るような $`\alpha`$ の集合を $`G_C`$ と書く。$`\le_1`$ では、$`\alpha \le_1^C \beta \Rightarrow \alpha \le_1^S \beta`$ が
  $`\beta \lt \kappa_C`$ のとき（**CORE-1**。どの $`\alpha`$ でも。Carlson 2009 の Def 9.1、Lemma 9.3、Thm 14.11 で示す）、
  $`\beta`$ が極限のとき（LIM1）、$`\beta = \alpha + 1`$ のとき（ONE-POINT）に成り立つ。$`\le_2`$ では、後続の段にはどちらの構造でも
  $`\le_2`$ の関係が無い（SUCC2）。$`\beta`$ がその $`\le_1`$ の前の元たちの極限なら逆向きが成り立つ（LIM2）。
- **DICH**（2026-10、査読 1 回）。$`\beta_0 \lt \infty`$ なら、ちょうど 1 つが成り立つ。(i) $`\beta_0 = \beta' + 1 \gt \kappa_C`$ で、
  食い違いは余分な $`\alpha \le_1^C \beta_0`$（$`\alpha \lt \beta'`$、$`\alpha \notin G_C`$）。(ii) $`\beta_0 = \omega^\lambda`$（$`\lambda`$ は極限）で、
  $`\beta_0`$ への $`\le_1`$ は一致し、食い違いは余分な $`\alpha \le_2^C \beta_0`$。$`\beta_0`$ の $`\le_1`$ の前の元には最大のもの
  $`d \lt \beta_0`$ があり、$`\alpha \le_2 d`$。だから $`\kappa_C`$ より下で 2 つの構造が最初に食い違うのは、(ii) の型の $`\le_2`$ の関係だけ。
- **R-INC**（2026-10、査読 1 回）。$`R_2^C`$ での主張を W(C)、「$`\kappa_C`$ 以下の段に (ii) の型の余分な $`\le_2^C`$ の関係が無い」を
  Σ2-GAP（査読者によれば $`\kappa_C \le \beta_0`$ と同値）、「どこでも $`\le_i^S \subseteq \le_i^C`$」を INC と書く。W(C)、Σ2-GAP、INC
  から AGR が出て、$`\mathrm{Core}(R_2^S) = \mathrm{Core}(R_2^C) = \rho`$。
- **(ii) の型の段**（2026-10、査読 1 回）。そういう段とは、$`\beta = \omega^\lambda`$（$`\lambda`$ は極限）で、$`\beta`$ より下のすべての組と
  $`\beta`$ への $`\le_1`$ で 2 つの構造が一致し、$`\beta`$ の $`\le_1`$ の前の元が空でなく有界で、その最大が $`d`$ であるもの。
  $`D_2 = \{\gamma \lt \beta : \gamma \le_2^C \beta\}`$ とする。
  - **MAX2。** $`D_2 \ne \emptyset`$ なら最大の元 $`a^* \le d`$ があり、$`\beta`$ での $`\le_2`$ の逆向きが $`D_2`$ 全体で成り立つことと
    $`a^* \le_2^S \beta`$ は同値。$`\beta_0`$ が (ii) の型なら、その余分な関係は $`(a^*, \beta_0)`$ にとれる。
  - **RED-d。** $`a^* \le_2^S \beta`$ は $`\Pi_2`$-UP($`\beta`$) と同値：$`a^*`$ 未満のパラメータを持つ $`\Pi_2`$ 文で $`R|d`$ で真のものは、
    どれも $`R|\beta`$ で真。手間が要るのは $`[d, \beta)`$ に触れる証拠だけ。**LOW-Y**：$`Y \subseteq [\alpha, d)`$ ならどれでも判定 T2 が
    成り立つ。
  - **FIRST2。** 最初の $`\lt_2`$ の組 $`(\upsilon_\omega, \upsilon_{\omega+1})`$ は (ii) の型の段で、$`a^* = d = \upsilon_\omega`$。査読者が足した
    （証明済み）：$`\upsilon_{\omega^2}`$ より下の (ii) の型の段ではどれも $`a^* = d`$。だから $`R_2`$ が分かっている段では、RED-d は何も
    減らさない。
  - **UPCOPY。** 核の中で：$`P`$ を isominimal、$`P`$ の中で $`a \lt_2 b`$、$`Y^\circ = P \cap [a, b)`$ とする。$`Y^\circ`$ の下向きの写しの
    「$`a`$ での」拡張（Carlson 2009, Def 8.6）はどれも、$`Y^\circ`$ のある上向きの写しの上で $`b`$ より下に現れる。その写しは
    $`P \cap b`$ 全体より上にあり、$`Y^\circ`$ そのものではない。
  - **EQ-E。** 次は同値：(E) $`\kappa_C \le \beta_0`$。Σ2-GAP。$`\kappa_C`$ 未満の (ii) の型のどの段 $`\beta`$ でも $`\Pi_2`$-UP($`\beta`$)。
    **予想 CORE-2**（核の中の一致する段で、$`\le_2^C`$ から $`\Sigma_2`$ 初等性が出る。Carlson 2001, Lemma 5.7(4) の 2 階の類似。
    Carlson 2009, 97 ページは、この同値を「別の所で示す」と言う）。
  - **R-OM。** (R)「$`\gamma \ge \kappa_C`$ のどれでも $`\kappa_C \le_1^S \gamma`$」は $`\kappa_C \le_1^S \Omega_1`$ と同値（[README-ja.md](README-ja.md) §3 の HULL からの
    $`\kappa_C \le \Omega_1`$ を使う）。(E) の下では、$`\gamma \in [\kappa_C, \beta_0]`$ のどれでも成り立つ。
  - **AGR は (E) かつ (R) と同値。** AGR に W(C) は要らない。要るのは「$`= \rho`$」のときだけ。
  - 未解決：**PIN**（拡張を上向きの写しから $`Y^\circ`$ そのものへ戻す）と **LOW**（新しい点が $`\max X`$ 以下にある拡張、
    または新しい点の最小が加法的主要数でない拡張）。示されているのは「PIN と LOW から CORE-2」の向きだけ。

## 9. 14 回目

4 つの論文（2026-10）。どれも 1 回ずつ査読された。だからこの節の結果は、回数を書いていなければ査読 1 回。**査読 2 回** とは、§1 の査読者が
移し替えとして認め、この回の査読者が全部書いた証明を確かめたもの。どの論文も、このページの最初に挙げた論文を使わない。Lean のファイルは
足していない：1 つの論文（§9.1）が名前を付けた点についての Lean の試験のファイルを leanman で確かめた（緑。査読者の再実行でも緑）が、標準形の判定の
試験用の写しで項を比べるだけなので、確かめた扱い。段の番号は §4 と同じく付け直した。

### 9.1 移し替えを全部書いた証明、$`\nu_P`$ までの名前、$`X_3`$ までの主張

記号は §1 と同じ。やり直し $`\lambda`$ について：$`s_2 = \upsilon_{\lambda+2}`$、$`\tau_1 = \upsilon_{\lambda+\omega}`$、$`\delta = \delta_\lambda = \upsilon_{\lambda+\omega+1}`$。$`R(\lambda)`$ は
[BREAK-ja.md](BREAK-ja.md) §4 の形式的な届く先。$`\Theta_{s2}`$ と $`\Theta_{\tau 1}`$ は、$`R(\lambda) \ge \delta + s_2`$、$`R(\lambda) \ge \delta + \tau_1`$ となる最小のやり直しの添字（$`\Theta_\delta`$、$`\Theta_{d\omega}`$ と同じ作り）。
$`\mathrm{cmax}(x)`$ は $`x`$ の標準形の、可算で極大な部分項の集合。$`\pi_g = \psi_{\Omega_2}(A_g)`$。

- **$`R`$ の定義の直し**（査読者：下のどの上からの半分もこれに依るので、書いておくこと）。$`R(\lambda)`$ は、[BREAK-ja.md](BREAK-ja.md) §4 の性質を持つ
  $`(\delta, \rho_{\lambda+\omega^2})`$ の中の最小の $`y`$。$`[\delta, \rho_{\lambda+\omega^2})`$ の中ではない。古い定義を文字どおり読むと、$`\mathrm{logend}(\eta_\lambda) = 2`$ のどのやり直しでも
  条件が空になって $`R(\lambda) = \delta`$ となり、下の証明の連なりが崩れる。直した $`R`$ は前の証明が使っていたもので、「届く先 $`\le R`$」がこれで成り立つ。
  これは [BREAK-ja.md](BREAK-ja.md) §4 の 1 つずれの直しで、それが認められた。
- **補題 S と COMP-S**（証明済み、査読 2 回）。$`\Omega_2`$ より下の任意の 2 つの $`\varepsilon`$ 数の基（可算でも非可算でも）と、狭義に増加し加法的で主要数を
  主要数に送る任意のパラメータの写像について、代入は Wilken の系の $`\lt`$ と $`+`$ の同型で、パラメータをその写像で動かす。代入を合成したものも代入。
  証明は Wilken 2007（APAL 145, 130–161）の L.5.3 に沿う。REN、SUBST-ISO、§1 の基 $`\theta`$ と $`G(\zeta)`$ での使い方はその特別な場合。
- **GEN⁺**（引用。GEN-ALL の場合でもある、[SHIFT5-ja.md](SHIFT5-ja.md) §1.3）：GEN-EXT（[BREAK-ja.md](BREAK-ja.md) §2）の $`\eta \lt \Omega_\omega`$ の場合。
- **SLOW$`_\zeta`$**（証明済み、査読 2 回）。LOW-STEP のどの補題（ARG、PMAX、Q、Q1、D、M）も、基 $`G(\zeta)`$ の段に書き直して証明した。
  （査読者：5.4 (ii) の 1 文は止まりの中の節について正しくない。その節は止まりより下にあるので結論は成り立つ。）
- **PHI、U\*、R-CAP**（証明済み、査読 2 回）。今は $`\lambda`$ についての 1 つの帰納法で、$`\kappa`$ は $`\varepsilon`$ 数、VIS は $`A_\eta`$ で使う（§1 の査読の細かい点
  m4、m5、m7）。FRAG は使わない。下からの評価：$`\Theta_{s2} \ge \iota'(\theta_2)`$、$`\Theta_{\tau 1} \ge \iota'(\theta_2\cdot\omega)`$、$`\Theta_\delta \ge \iota'(\theta_2\cdot(\omega+1))`$、$`\Theta_{d\omega} \ge \iota'(\eta_{d\omega})`$、
  $`\Lambda^* \ge \iota'(\theta_2\cdot\omega^2)`$。
- **SSTEP$`_\zeta`$**（証明済み）。定理 STEP を 1 段上げたもの：基 $`G(\zeta)`$ での写像 $`B`$（$`X_0 = \Omega_\omega + \theta_2\cdot\zeta`$、段 0 の符号は $`\psi_{\Omega_3}(\omega^{B(\alpha)})`$）は
  狭義に増加し、$`G(\zeta+1)`$ の中に入る。だから $`T^{G(\zeta)} \cap \Omega_2 \le G(\zeta+1)`$。逆の不等式は未解決で、使っていない：上限より下のどの順序数も要るが、
  補題 IS は可算個しか扱わない。**正誤**：[VEBLEN-ja.md](VEBLEN-ja.md) §8 の L3 も同じ理由で、証明されているのは $`T^{\Omega_1} \cap \Omega_2 \le \theta`$ だけで、等号ではない。等号を使う所は無い。
- **補題 C、実現する写像、B-PAR、HULL-SEG、REAL、補題 L$`_R`$、BRACKET**（証明済み）。やり直しのずれは Wilken の項を通して読む（補題 C）。
  実現する写像はずれをやり直しの指数に送り、パラメータを抑える（B-PAR。査読者：補題 S は Wilken の項について証明されているので、帰納法は同時に
  定めた系の項の上で回すこと）。HULL-SEG：

```math
C_g \cap \Omega_2 = \{\, x \lt \pi_g : \mathrm{cmax}(x) \subseteq H(g) \,\}.
```

  REAL：実現するものは共終に在る（査読者：$`\nu \le \eta_0`$ についてだけ。使う所はそれで足りる）。補題 L$`_R`$（論文の「補題 L」。[README-ja.md](README-ja.md) §3 の
  Lean の補題 L と重なるので名前を変えた）：指数がずれ $`m`$ の像であるどのやり直し $`\mu`$ でも、FRAG 無しで $`R(\mu) \ge \delta_\mu + c_\mu(m)`$。FRAG のもとで届く先も同じ。
  BRACKET：2 つの写像から $`R(\lambda) - \delta`$ の上下の評価。（査読者：補題 L$`_R`$ の最初の場合は、前の別の補題を引くべき。結論は同じ。15 回目に直した：logend が 2 のやり直しでは
  $`\delta`$ は反映されないので、最初の場合はブロックの的についての歩みの補題（歩み 1）を使う、[SHIFT-ja.md](SHIFT-ja.md) §1。）
- **NAMES-EQ**（証明済み。査読者はどの行も両方の半分を確かめた）。$`\eta_{d\omega} = \omega^{\theta_2+1} + \theta_2 + \omega^{\omega^{G+1}}`$、
  $`G = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$ として：

| やり直し | 添字 | $`\rho`$ | $`R`$ | FRAG |
|---|---|---|---|---|
| $`\Theta_{s2}`$ | $`\iota'(\theta_2)`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta_2)`$ | $`\delta + s_2`$ | 使わない |
| $`\Theta_{\tau 1}`$ | $`\iota'(\theta_2\cdot\omega)`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1})`$ | $`\delta + \tau_1`$ | 使わない |
| $`\Theta_\delta`$ | $`\iota'(\theta_2\cdot(\omega+1))`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+1} + \theta_2)`$ | $`\delta\cdot 2`$ | 使わない |
| $`\Theta_{d\omega}`$ | $`\iota'(\eta_{d\omega})`$ | $`\psi_{\Omega_1}(\Omega_\omega + \eta_{d\omega})`$ | $`[\delta\cdot\omega, \delta_2)`$ の中 | 使わない |
| $`\Lambda^*`$ | $`\iota'(\theta_2\cdot\omega^2)`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2})`$ | | 上の半分 |
| $`\Lambda^* + \omega^2`$ | | $`\nu_P = X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ | | 上の半分 |

- だから §1 で予想した名前は証明された（FRAG は証明済み、[BREAK-ja.md](BREAK-ja.md) §4）。$`\Theta_{d\omega}`$ では、素の写像が行き過ぎるので、混ぜた実現するもの
  （$`G`$ の倍数と像の和）が要る。$`R(\Theta_{d\omega})`$ の値は決まっていない。
- **定理 X3**（証明済み、FRAG 無し）。$`\lambda_2 = \iota'(\theta_2\cdot\omega^2)`$ として：

```math
\nu_C \ge X_3 = \upsilon_{\lambda_2+\omega^3\cdot 2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2).
```

  証明：R-CAP と、NU-CT（[BREAK-ja.md](BREAK-ja.md) §2）のどちらの場合でも、$`\nu_C`$ での組の左端は $`\omega^3 \mid L \gt \lambda_2`$ となる $`\rho_L`$ で、右端の添字は
  $`L + \omega^3`$ 以上であること（FIRST-PAIR と補題 GHOST、[BREAK-ja.md](BREAK-ja.md) §2）。（査読者：場合 (A) は $`\nu_C = \nu_S`$ を通して $`R_2^S`$ の事実を使う。正しいが、
  そう書くこと。）だから **$`R_2^C`$ での Wilken の主張は $`[0, X_3]`$ で両方の半分とも成り立つ**（FRAG 無し）：核の側は $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$ から、名前の側は
  補題 L と IS から。$`[0, \nu_P] = [0, X_2]`$ でも成り立つ（査読 2 回：§1 で移し替えとして、ここで全部書いて）。
- **未解決**：$`\nu_C`$ の InaccPsi による上からの評価。実現するもの、上向きと下向きの写し、ねじれた写し TW-0 は、$`\le_1`$ の事実か、在ると分かっている
  $`\lt_2`$ の組の写ししか出さない。名前の付いた評価には、$`b`$ に名前の付いた新しい組 $`\rho_L \lt_2 b`$ が 1 つ要る：Wilken 2020, Thm 21.13 のように、終わりの区間
  $`[\rho_L, b)`$ を $`\rho_L`$ の $`\le_1`$ の前の点の上の区間へ移す同型（そうすれば Prop 21.11 が組を出す）。候補の組は予想 NU-NAME（[BREAK-ja.md](BREAK-ja.md) §2）の
  $`a_0 \lt_2 \nu`$。（今は $`\nu_C \ge X_4`$ で、新しい組は要らない：名前の付いた 1 つの組での 2 つの $`\le_1`$ の命題が評価を与える、
  [SHIFT-ja.md](SHIFT-ja.md) §1。さらに FRAG のもとで $`\nu_C \ge X_5`$ で、2 つの命題はまだ未解決、そこの §8.1。さらに FRAG のもとで $`\nu_C \ge X_8`$ で、(P) には非可算のずれを越える届く先が要る、そこの §9.1。さらに FRAG のもとで $`\nu_C \ge X_9`$、[SHIFT2-ja.md](SHIFT2-ja.md) §1.1。さらに FRAG のもとで $`\nu_C \ge X_{11}`$、そこの §2.1。さらに FRAG のもとで $`\nu_C \ge X_{12}`$、そこの §3.1。さらに FRAG のもとで $`\nu_C \ge X_{13}`$、[SHIFT3-ja.md](SHIFT3-ja.md) §1.1。さらに FRAG のもとで $`\nu_C \ge X_{14}`$、そこの §2.1。さらに FRAG のもとで $`\nu_C \ge X_{15}`$、[SHIFT4-ja.md](SHIFT4-ja.md) §1.1。さらに FRAG のもとで $`\nu_C \ge X_{16}`$、そこの §1.4。さらに FRAG のもとで $`\nu_C \ge X_{17}`$ と $`\nu_C \ge X_{18}`$、そこの §2.1、§2.2。さらに FRAG のもとで $`\nu_C \ge X_{19}`$、[SHIFT5-ja.md](SHIFT5-ja.md) §1.1。さらに FRAG のもとで $`\nu_C \ge X_{21}`$、そこの §2.1。さらに FRAG のもとで $`\nu_C \ge X_{22}`$ と $`\nu_C \ge X_{23}`$、[SHIFT6-ja.md](SHIFT6-ja.md) §1.1、§2.1 と、そこの §3.1 の直し。さらに FRAG のもとで $`\nu_C \ge L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P')`$、[SHIFT7-ja.md](SHIFT7-ja.md) §1.1。さらに FRAG のもとで $`\nu_C = \nu_S = L(\omega+1)`$、そこの §2.1（監査はそこの §3.1）。）ほかに未解決：$`R(\Theta_{d\omega})`$ の値、最初の新しい組の左端の最小の $`\le_1`$ の前の点 $`m_0`$ について $`m_0 \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ かどうか。

### 9.2 素の符号：$`\Lambda_T`$ までの部品

記号は §2 と同じ。$`F(\alpha) = \upsilon_{1+\alpha}`$。正規な写像 $`H`$ について：$`O_1(H)`$ は $`H`$ の不動点を数え上げる；$`O_{n+1}(H)`$ は $`O_n^z(H)(0) = z`$ となる $`z`$ を
数え上げる；$`S(H)`$ はすべての $`O_n(H)`$ に共通の値を数え上げる；$`T(H)`$ は $`S^z(H)(0) = z`$ となる $`z`$ を数え上げる。だから $`\Gamma^\upsilon_1 = O_2(F)(0)`$。$`\Lambda_T = T^{\omega^2}(F)(0)`$。

- **MODULE-RED⁺**（含意として証明済み）。§2 の MODULE-RED は、形 (MA⁺) のどの部品でも成り立つ：$`r \lt x \lt_2 y`$、$`r`$ と $`x`$ はいちばん上 $`R`$ に $`\le_1`$、
  そして $`(y, R]`$ のある $`c`$ が $`A \ge r`$、$`c + A \le R`$ で $`c \le_1 c + A`$。これで、内側の鎖がいくつもあるもの、入れ子の組、$`x`$ を含む和、conv の部品
  $`c \le_1 c + y`$ と $`c \le_1 c\cdot 2`$ が許される。EXIST-AMB には §2 の査読が求めた場合を足した。（査読者：ほかの組はすべて $`(x, y)`$ にあるという注意には
  「$`(r, x)`$ に元が無い」が要る。どの証明も使わない。）
- **CHAIN⁺**（証明済み）。$`c \le_1 c + A`$ を持つ部品は、どれも 1 つの飾り $`u \le_1 u + D`$（$`D`$ は $`u`$ を含んでもよい）を持つ部品の入れ子を、どの $`D`$ も
  宿り先で読んで $`A`$ より小さい限り、すべて宿す。（査読者：[VEBLEN-ja.md](VEBLEN-ja.md) §9 の CHAIN はこの最初の場合で、特別な場合ではない。）
- **DOM-T、NO-HIGH-T**（証明済み）。$`\Lambda_T`$ より下の $`\upsilon`$ のどの不動点にも決まったデータ（$`\omega^2`$ より下の層、水準、貪欲な署名）があり、2 つの不動点は
  データで比べられる。
- **LEX-HOST、(MC)、定理 IDX-T**（証明済み）。型 T の部品：有限の位置は部品の入れ子で、層と水準は飾りで符号にする。だから素の符号は
  $`[\omega, \Lambda_T)`$ で順序が付き、素の符号で

```math
\iota(\mathrm{CH}_2) \ge \Lambda_T \gt T^\omega(F)(0) \gt T(F)(0) \gt S(F)(0) \gt \Gamma^\upsilon_1 = \Lambda_\Gamma.
```

  （査読者：(0,0,0)(1,1,1)(2,1,1)(3,1,1) と (0,0,0)(1,1,1)(2,2,0) の conv のパターンについての同じ評価は、部品のパターンについて証明済み。それが conv の出力と
  等しいことは確かめただけ。）予想する名前は、$`H'(\Delta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Delta})`$ として $`O_n(F)(0) = H'(\Omega_1^n)`$、$`S(F)(0) = H'(\Omega_1^\omega)`$、
  $`T(F)(0) = H'(\Omega_1^{\omega+1})`$、$`\Lambda_T = H'(\Omega_1^{\omega+1}\cdot\omega^2)`$。まだ $`\Lambda_\varepsilon \lt \nu_C`$ よりずっと下で、進んだのは素の道だけ。
- **数えない**（査読者：2 つの証明の方法についての注意）：「$`\Lambda_T`$ の部品は CHAIN⁺ でも LEX-HOST でも作れない」。
- **未解決**：$`\Lambda_T`$ そのものの部品：いくつもの枠を持つ飾り（あらすじ。2 枠は紙の上で確かめた）、次に CHAIN-REL（外側の $`x`$ を使う内側の部分を宿すこと。
  そこでは GEN (a) が使えない）。(G2)：$`\upsilon`$ の上のつぶす関数 $`\vartheta^\upsilon`$ を定め、比べる補題・対応表・名前は予想。DOM-T はその補題の片方の向きの
  類似（査読者）。届く先は $`\Theta_1`$ と予想。$`\iota(\mathrm{CH}_2) \ge \theta_0`$ は未解決のまま。

### 9.3 $`\Phi_3`$ の形：入れ子の部品、3,166 個のうち 2,330 個

記号は §3 と同じ。

- **OPQ-R**（メタの証明済み）と **LEMMA OPEN**（証明済み）。書き換えたプログラムを、中の見えない頭の部分、開いた繰り返しの数、階段の区間を持つ項で
  走らせると、どの具体例でも結果が出る。（査読者：コードは最初の繰り返ししか開かない。下の行列のために作ったどの開いた項も繰り返しは高々 1 つ。）
- **定理 NB**（証明済み。LEMMA SLOT の (a) は書かれたままでは偽で、155 個すべてで確かめた査読者の直しで、それと NB が証明済みになる）。
  繰り返しが根の子の中にある M1 の行列について：$`V(A[n]) = V_{base} \cup \beta(0) \cup \dots \cup \beta(n)`$。どのブロック $`\beta(j)`$ も族の枠を持つ決まった節の並びで、
  族のどの元もまたそういう並び（だからブロックは倍々に増える）。
- **NB-DER**（証明済み）。どのブロックの型も、行列のいちばん上のブロックの長い組 $`x \lt_2 y`$ に写り、GEN で conv$`(A[n]) \ll`$ conv$`(A)`$。155 個の行列。
- **SUM-CORE-NB**（26 個）、**IX-NB**（59 個。その補題 IX-PHI\* はあらすじしか書いていない）、**SUM-CORE-2**（30 個）、**IX-STAIR**（73 個）、そして $`(0,0,0)(1,1,1)`$ を
  階段の芯とすること（73 個のうち 39 個）：証明済み。
- **未証明**：2.6 の GEN の帰納法（繰り返しの数が減ることを確かめていない）。数えたどの行列も使わない。（今は証明済みの GEN-IND に
  置き換えた、[SHIFT-ja.md](SHIFT-ja.md) §3。）
- **集計**（査読者が再現した。$`2{,}330 = 1{,}987 + 343`$）：

| 類 | 行列 | どの $`n`$ でも証明済み | 小さい $`n`$ で確かめた条件のもと | $`t = 2`$、小さい $`n`$ で確かめた形のもと | 未解決 |
|---|---|---|---|---|---|
| I | 581 | 479 | 0 | 0 | 102 |
| SUM | 603 | 544 | 7 | 0 | 52 |
| ROOT | 635 | 587 | 0 | 0 | 48 |
| III | 1,347 | 720 | 0 | 24 | 603 |
| 全部 | 3,166 | 2,330 | 7 | 24 | 805 |

- §3 の「LOW のもと」の 2 個は新しく証明したものに入る。**残り**（836 個）：M1 18 個（届く先が小さいすべての繰り返しの長さを通って再帰する 5 個、それを芯に
  持つ 6 個、型が最初のブロックで崩れる 1 個、SUM 3 個、型の節が芯より下にある 3 個）；M2 139、M3 28、M4 14、M5 23；$`t = 2`$：III 160、ROOT 31、I 15、SUM 26；
  $`t = 1`$：382。§3 の査読の細かい点 m1〜m6 は正誤として反映した。

### 9.4 $`\nu_C = \nu_S`$：ねじれた写し

記号は §4 と同じ。

- **PUSH**（証明済み）。$`u_{m+1} \le_1 x`$。だから $`U_2`$ のどの点もねじれた写しを要らない：(TWIST\*) の「点 $`u_{m+j}`$」の場合は起きない。
- **TOPSUM、REACH-RED、TW-CLASS**（証明済み。Wilken 2007, APAL 145, 162–175, Thm 2.2 の引用は論文と一致する）。(CUT′) は届く先の正確な移し替えから出る：
  $`\mathrm{lh}(\Psi_0(a)) = \Psi_0(L_{top}) + T_m(L_{low})`$。ねじれた三つ組はねじれた点にしか起きず、ねじれた点は閉じた形で分類される。
- **LADDER、DIAG、FIX-LADDER、LH-DELTA**（証明済み。1 つの段は定理 KV の直せる書き損じを受け継ぐ、[FANFREE-ja.md](FANFREE-ja.md) §10.3）。添字が対角の類
  $`\mathrm{Fix}(f_\Delta)`$ に無いどのやり直しも、$`\delta\cdot 2`$ より下の閉じた届く先を持つ。長いやり直し、$`U_2`$ の点、$`\nu`$ の添字はこの類にある。
- **NU-K**（証明済み）。長いやり直しは $`\nu`$ の下で共終（Carlson 2009, Def 5.3 の 2 つ目の項）。
- **FRESH**：書かれたままでは未証明（段 0 で新しい添字がやり直しの添字にならないことがある）。査読者が 1 行の直しを出した。**TW-MULTI**（その直しと
  もう 1 つの直しで証明済み）：小さい閉じた形のやり直しの骨組みの有限の和には、ねじれた写しがある。だからいくつものブロックを一度に、
  $`\mathrm{Fix}_1 \setminus K`$ のやり直し、$`\mathrm{Fix}(f_\Delta)`$ の外の $`K`$ の点で成り立つ。**TW-MIX**（繰り返しを増える順に作れば証明済み）：これらの写しは、4 つの条件の
  もとで、錨の上の Carlson の写しと組み合わさる。
- **DICT、PROF-1**（証明済み）。$`u`$ 以上の位置が高々 1 つの記号では (PROF) が成り立つ。
- **未証明**：一般の (TWIST\*)。残り：添字が $`\mathrm{Fix}(f_\Delta)`$ にあるねじれた点（長いやり直しを含む）、いちばん上のデータ、繰り返しの区域にあって骨組みに無い点
  （ねじれていてもいなくても。査読者の例 $`\omega^{\rho_a+1}`$ は、論文の残りのリストが全部ではないことを示す）、条件 SEP と ROOM が崩れる場合。$`u`$ 以上の位置が
  2 つ以上の (PROF) と、$`u^\#`$ より先の基の取り替えは未解決。$`\nu_C = \nu_S`$ も $`\nu_C \lt \nu_S`$ も証明されていない。

### 9.5 14 回目のあとの状態

15〜35 回目でこの状態は変わった。[SHIFT-ja.md](SHIFT-ja.md) の §5、§8.5、§9.5、[SHIFT2-ja.md](SHIFT2-ja.md) §1.5、§2.5、§3.5、[SHIFT3-ja.md](SHIFT3-ja.md) §1.5、§2.5、[SHIFT4-ja.md](SHIFT4-ja.md) §1.5、§2.5、[SHIFT5-ja.md](SHIFT5-ja.md) §1.4、§2.4 と [SHIFT6-ja.md](SHIFT6-ja.md) §1.4、§2.4、§3.4、[SHIFT7-ja.md](SHIFT7-ja.md) §1.4、§2.4、§3.4、[SHIFT8-ja.md](SHIFT8-ja.md) §1.4、§2.4、[SHIFT9-ja.md](SHIFT9-ja.md) §1.4 を見よ。

- $`R_2^C`$ での Wilken の主張：$`X_3 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$ として $`[0, X_3]`$ で両方の半分とも成り立つ。FRAG も移し替えも残っていない。
  $`\Theta_\delta`$、$`\Theta_{d\omega}`$、$`\Lambda^*`$、$`\nu_P = X_2`$ の名前は証明済み。核の側は $`\nu_C \ge X_3`$ として $`[0, \nu_C]`$ で成り立つ。
- $`\theta_0`$ より下の下からの評価のための計画：SRO より下の段は、標本 3,166 個のうち 2,330 個ですべての $`n`$ で証明済み。素の符号で $`\iota(\mathrm{CH}_2) \ge \Lambda_T`$。
- 上からの評価：$`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ の InaccPsi の項による評価はまだ無い。
- $`\nu_C = \nu_S`$：小さい閉じた形の骨組みにはねじれた写しがある。残り：$`\mathrm{Fix}(f_\Delta)`$ での残り、SEP、ROOM、(PROF)。

### 9.6 14 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。証明書は再生されたものだけを数える。

- §9.1。基 $`G(0)`$、$`G(1)`$、$`G(\omega)`$、$`G(\omega+1)`$ でのずらした写像 $`B`$：1,278,400 組で失敗 0。2 つの壊した対照は失敗する。同値の形の B-PAR：9,000 組で食い違い 0。
  HULL-SEG：33,800 組で食い違い 0。名前を付けた 9 個の点は標準形で増加する。査読者：4 つの基の 2,995 個の項で $`E(B(t)) \ge t`$（崩れると BRACKET が矛盾する）、
  REAL のとおりに作った 1,200 個の実現するものがすべて正しい、実行の再現で食い違い 0。
- §9.2。23 個の部品（新しいのは 19 個）はパターンで、RF、扇無し、L1p 無し。4 個は conv の出力と等しい。証明書：予想した向きで 20 組中 18 組、CHAIN⁺ で
  7 組中 5 組、すべて再生済み。逆向きは 6 組中 0 組。査読者の再実行は同じで、自前の逆向きの探索 5 個は何も見つけなかった（どれも 45 秒で止めた）。
- §9.3。$`n = 6, 7`$ の全部の構成の節の集合は NB の 155 個すべてで一致し（節の集合だけ）、132 個の添字の型も一致する。査読者：lh と succ 付きの順序の並びが $`j = 6, 7`$（155 個中 155 個）と
  $`j = 8`$（52 個中 52 個）で一致；型は $`n = 8, 9`$ で正しい；$`(0,0,0)(1,1,1)`$ は $`n = 2, \ldots, 20`$ で段を通る。
- §9.4。K(3,0,0)、K(3,0,0)(3,0,0)、K(3,1,0) の読みは LADDER と DIAG に合う。査読者：プログラムで 18 個の列を読み、新しい 4 つの予想にも合った。

### 9.7 未解決

15〜35 回目でこのリストは変わった。今のリストは [SHIFT9-ja.md](SHIFT9-ja.md) §1.6。

- 上からの評価：$`\nu_C`$ の InaccPsi による評価（名前の付いた $`b`$ での新しい組 $`\rho_L \lt_2 b`$ が 1 つ、§9.1）、$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価。
- 最初の到達不能基数：$`H_m`$。$`\iota(\mathrm{CH}_2) \ge \theta_0`$ を通して（$`\Lambda_T`$ から先の部品：いくつもの枠、CHAIN-REL、またはつぶす関数 $`\vartheta^\upsilon`$）。
  §9.3 の 836 個の行列での SRO より下の UNIF-FS。
- $`\nu_C = \nu_S`$：$`\mathrm{Fix}(f_\Delta)`$ での (TWIST\*) と骨組みの外の点、SEP と ROOM、位置が 2 つ以上の (PROF)。
- 名前：$`R(\Theta_{d\omega})`$；$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ；$`X_3`$ より先の名前；[COVER-ja.md](COVER-ja.md) §9 の残り。
