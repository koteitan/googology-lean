[← Back](README-ja.md) | [English](VEBLEN.md) | [Japanese](VEBLEN-ja.md)

# $`R_2^+`$ の 11 回目：Γ より先のずれ、$`\upsilon_1`$ までの素の符号、$`\Phi_3`$ の形のための周期的な記号、直接の $`\Sigma_2`$ の議論

このページは [FANFREE-ja.md](FANFREE-ja.md) の続き。状態の言葉は [README-ja.md](README-ja.md) の §3 と同じ：**証明済み**は、独立した査読者が、
致命的な点も止める点も無く証明済みと判定したもの。このページの結果はどれも 2026-10 のもので、11 回目の 4 つの論文から来ている。
止める点のある命題は **未証明** に、査読者が目標の言い直しや自明と判定した命題は **数えない** に書く。証明書は再生されたものだけを数える。
どの論文も Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わず、Carlson 2009, p. 97 が予告する同値も使わない。
このページの結果はどれも Lean には無く、Lean のファイルは足していない。記号は [FANFREE-ja.md](FANFREE-ja.md) と同じ。

4 つの論文で、どれも 1 回ずつ査読された。だからここの結果はどれも査読 1 回。1 つの論文（§1）は、名前を付けた点についての Lean の
試験のファイルを leanman で確かめた（緑。査読者の再実行でも緑）。このファイルは項を比べるだけで（`#eval` だけで定理は無い）、ライブラリには
足していない。ほかの 3 つの論文は Lean について何も主張しない。論文は段を 1 つ小さく数えるので、ここでは番号を付け直した（下の $`U_2`$ の点は、
論文の 1 つ目の段の点）。

## 1. Γ より先のずれと、$`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$ までの主張

記号は [FANFREE-ja.md](FANFREE-ja.md) §10.4 と同じ。強臨界な順序数とは $`\Gamma`$ の値のことで、$`\Gamma_a`$ はその $`a`$ 番目。$`\Gamma_X = X`$ のとき $`X`$ は Γ で動かないと言い、
$`\Gamma^{\mathrm{fp}}(x)`$ は $`x`$ より上で Γ で動かない最小の順序数。$`\bar\varphi_\delta`$ は、$`\varphi_\delta`$ の値で $`\varphi_\delta`$ の不動点でないものを順に並べる。
$`\vartheta^\tau`$ は基 $`\tau`$ の上の Wilken のつぶす関数（Wilken 2007, APAL 145, 130–161）。項 $`t`$ について、$`t[\Omega_1 := r]`$ は $`\Omega_1`$ を $`r`$ に、$`\Gamma_a`$ を
$`\Gamma_{a[\Omega_1 := r]}`$ に、$`\psi_{\Omega_2}(\Omega_2)`$ を $`\Gamma^{\mathrm{fp}}(r)`$ に置き換える。

- **[FANFREE-ja.md](FANFREE-ja.md) §10.4 の修理**（証明済み）。ATTAIN-NAMES は仮定 $`\omega^{1+t} \in D`$ を足せば成り立つ（たとえば $`t`$ のどの定数も $`\upsilon_1`$ より下）。$`\Theta_1 \gt \Lambda' + \omega^2`$、
  だから $`\rho_{\Theta_1} \gt \rho_{\Lambda'+\omega^2}`$。NAME-LAYERS で $`e`$ が決めるのは、残りの部分については logend までだけ。[FANFREE-ja.md](FANFREE-ja.md) §10.4 の査読者の注意は今は証明
  済み：主張は $`[0, H(\varepsilon_{\zeta_{\Omega_1+1}+1}\cdot\omega + \omega^2))`$ で成り立っていた。
- **VEB-THETA**（証明済み。Wilken 2007 の L.3.5、3.7、3.30、4.3、4.4 から）。$`\tau`$ を 1 か $`\upsilon^*`$ より下の $`\upsilon`$ 点とする。$`1 \le \delta \lt \tau^\infty`$ と
  $`\eta \lt \tau^\infty`$ で $`\vartheta^\tau(\Omega_1\cdot\delta + \eta) = \bar\varphi_\delta(o_\delta + \eta)`$。ここで $`o_\delta`$ は、$`\delta \lt \tau`$ なら $`\tau`$、$`\delta \ge \tau`$ が強臨界なら 1、
  それ以外は 0。だから Wilken の系の段 $`\Omega_1\cdot\delta`$ は、不動点を除いた $`\delta`$ 番目の Veblen 関数で、強臨界な順序数はちょうど段が $`\Omega_1^2`$ 以上の値。
  [FANFREE-ja.md](FANFREE-ja.md) §10.4 の EPS-THETA は $`\delta = 1`$ の場合。（査読者：補題 FIXP の証明の不等式の 1 つは $`\delta`$ が強臨界のとき偽。要る事実は成り立つ。）
- **GC と GAM-THETA**（証明済み）。どの $`\upsilon`$ 点も Γ で動かない。$`\Gamma^{\mathrm{fp}}(\tau) = \vartheta^\tau(\Omega_1^2 + \Omega_1)`$ で、$`\vartheta^\tau(\Omega_1^2 + \eta)`$ が
  $`\Gamma^{\mathrm{fp}}(\tau)`$ より下のあいだは $`\Gamma_{\tau+1+\eta}`$ に等しい。
- **EXACT-G**（証明済み）。$`\upsilon`$ 点 $`s \lt r`$ について、$`r`$ から $`s`$ への Wilken の基の取り替えは、$`s`$ より下の定数、基、$`+`$、$`\varphi`$、基の
  $`\Gamma^{\mathrm{fp}}`$ より下の $`a \mapsto \Gamma_a`$ から作ったどの項でも、また基の $`\Gamma^{\mathrm{fp}}`$ とそれに 1 を足したものでも正確（前は EXACT-Z で、
  $`\varepsilon_{\zeta^x+1}`$ より下の $`\varepsilon`$ まで）。
- **PSI2 と InaccPsi の側**（証明済み）。$`\beta \lt \psi_{\Omega_2}(\Omega_2)`$ で $`\psi_{\Omega_2}(\beta) = \Gamma_{\Omega_1+1+\beta}`$、そして $`\psi_{\Omega_2}(\Omega_2) = \Gamma^{\mathrm{fp}}(\Omega_1)`$。
  包の元の Veblen の成分と Γ の添字は包に残る（COMP-V、COMP-G）。これらの項の標準形は、Γ で動かないどの強臨界な基でも同じように比べられる
  （UNIF-G）。TERM-G と包の閉じ方。（査読者：UNIF-G の帰納法の測り方は変える必要がある。先に標準形を決め、それから比べる。命題は正しい。）
- **定理 NAME-OFFSET-G**（証明済み）。$`\rho_\lambda \lt \upsilon^*`$ で $`e_\lambda \le \psi_{\Omega_2}(\Omega_2) + 1`$ のどのやり直しの添字 $`\lambda`$ でも
  $`c^+(\lambda) = (-1 + e_\lambda)[\Omega_1 := \rho_\lambda]`$。これは [FANFREE-ja.md](FANFREE-ja.md) §10.4 の NAME-OFFSET-Z を含む。
- **目印**（証明済み）。$`c^+ = \Gamma_{\rho+1}`$ となる最初のやり直しの点は $`H(\Gamma_{\Omega_1+1}) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(0)})`$。
  $`c^+ = \Gamma_{\rho\cdot 2}`$ では $`H(\psi_{\Omega_2}(\Omega_1))`$。$`c^+ = \Gamma^{\mathrm{fp}}(\rho)`$ では $`H(\psi_{\Omega_2}(\Omega_2))`$。$`c^+ = \Gamma^{\mathrm{fp}}(\rho) + 1`$ では
  $`\Lambda_{\mathrm{fp}} = H(\psi_{\Omega_2}(\Omega_2)\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2)+1})`$。つまり $`\Lambda_{\mathrm{fp}}`$ と $`\Gamma^{\mathrm{fp}}`$ の関係は、
  $`\Lambda_\varepsilon`$ と $`\alpha \mapsto \varepsilon_{\alpha+1}`$ の関係と同じ。そして $`\Theta_1 \gt \Lambda_{\mathrm{fp}} + \omega^2`$。（査読者：$`\omega^{\psi_{\Omega_2}(\Omega_2)+1} \in D`$ に引用した
  場所はそれを含まない。1 行の修理で出る。）
- **STRUCT″**（証明済み）。[FANFREE-ja.md](FANFREE-ja.md) §10.4 の STRUCT′ が $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$ で、$`R_2^C`$ でも $`R_2^S`$ でも成り立ち、どのやり直しの点の届く先も
  NAME-OFFSET-G で閉じた形になる。（査読者：そこで 2 つの構造が一致することは EQB-A で、補題 FRAG が要る。FRAG は証明済み。）
- **$`R_2^C`$ での $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$ の上の Wilken の主張**、両方の半分とも（証明済み）：
  $`\rho_{\Lambda_{\mathrm{fp}}+\omega^2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\psi_{\Omega_2}(\Omega_2)+1} + \omega^{\theta+2})`$ より下のどの順序数も核に入り、つぶす引数が $`I_\omega`$ より
  小さい InaccPsi の標準形の値。前は $`[0, \rho_{\Lambda'+\omega^2})`$。[FANFREE-ja.md](FANFREE-ja.md) §10.4 と同じく、主張にとって新しい事実は位置 $`\Lambda_{\mathrm{fp}} + \omega^2 \lt \Theta_1`$。
  **注意**（査読者のもので、数えない）：同じ証明でずれ $`\psi_{\Omega_2}(\Omega_2) + c`$（$`c \lt \omega`$）まで届き、たぶん $`\Gamma_{\Gamma^{\mathrm{fp}}(x)+1}`$ より下のどの
  ずれまでも届く。
- **定理 KV-NAMES**（[FANFREE-ja.md](FANFREE-ja.md) §10.3 の定理 KV とその修理のもとで証明済み）。$`\rho_\lambda \lt \min(\nu_C, \upsilon^*)`$ のどのやり直しの添字 $`\lambda`$ でも、
  $`e = e_\lambda`$ とすると：$`\lambda \notin \mathrm{Fix}_1`$ なら $`e = \mathrm{logend}(\lambda)`$。$`\lambda \in \mathrm{Fix}_1 \setminus K`$ が標準の形 $`(A, \eta)`$ を持つなら
  $`e = P_A(\Omega_1) + \mathrm{logend}(\eta)`$。$`\lambda \in K`$ は $`e \ge \Omega_1^{\Omega_1}`$ と同じ。成分が $`\lambda`$ より下のどの記号 $`B \ne 0`$ でも、$`\lambda \in F_B`$ は
  $`e \ge P_B(\Omega_1)`$ と同じ。だから KV の Klammer の届く先は InaccPsi の名前で書ける：$`\mathrm{lh}(\rho_\lambda) = H(\eta_\lambda + \omega + 1) + P_A(\rho) + \mathrm{logend}(\eta)`$。
  この範囲で、$`\iota(\eta)`$ の Klammer の形は $`\mathrm{logend}(\eta)`$ の $`\Omega_1`$ 進展開だという予想が証明された。NAME-LAYERS は位置が 3 以下の場合。
  $`K`$ の最初の点は $`H(\omega^{\Omega_1^{\Omega_1}})`$。$`\nu_C \lt \upsilon^*`$ かどうかは未解決。
- **$`\Theta_1`$**（帰着として証明済み）。基 $`\Omega_1`$ の上の Wilken の系を $`T^{\Omega_1}`$ とする。**H3**（ずらした STEP-0、証明済み）：
  $`T^{\Omega_1} \cap \Omega_2 \le \theta`$。**THETA1-RED**（含意として証明済み）：(H2b) から $`\Theta_1 \le \iota(\theta)`$。(H2a) から $`\Theta_1 \ge \iota(\theta)`$ と
  $`[0, H(\theta))`$ での主張。両方で $`\Theta_1 = H(\theta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta\cdot 2})`$。(H2a) と (H2b) を合わせると、$`(\Omega_\omega + \theta\cdot g, H(g))`$ の
  InaccPsi の包と Wilken の包 $`T^{\Omega_1}[H(g)]`$ が $`\theta`$ より下で同じ元を持つ、という命題。
- **未証明**：$`\Theta_1 = H(\theta)`$ と $`[0, H(\theta))`$ での主張。論文の言うとおり、(H2a) と (H2b) は $`\psi_{\Omega_2}(\Omega_2)`$ より先で未解決。論文の文
  「(H2a) と (H2b) は $`[0, \psi_{\Omega_2}(\Omega_2)]`$ で成り立つ」も証明されていない（(H2b) の片方の向きと、ずらした VEB-THETA が言われているだけ）。
  証明済みの結果でそれを使うものは無い。
- **$`U_2`$ の点と長いやり直しの点**（証明済み）。$`\upsilon^*`$ より下の $`U_2`$ のどの点も、$`\min(\nu_C, \upsilon^*)`$ より下のどの長いやり直しの点も、
  $`\mathrm{logend}(\eta) \gt \psi_{\Omega_2}(\Omega_2) + 1`$ の $`H(\eta)`$（(H2a) のもとでは $`\ge \theta`$）。
- **未解決**：$`\nu_C`$ の InaccPsi による上からの評価。それには、名前のある区域 C の点（$`\Theta_1`$ より上で、届く先が分かっていない所）で、正の関係、
  つまりもう 1 つの組を含む $`\lt_2`$ の組が要る。

## 2. $`\upsilon_1`$ までの素の符号と、1 段の参照

記号は [FANFREE-ja.md](FANFREE-ja.md) §10.2 と同じ。$`\varepsilon`$ 数 $`x = \vartheta(D_x + \eta_x)`$（$`D_x`$ は $`\Omega_1`$ の倍数、$`\eta_x \lt \Omega_1`$）について $`x^+ = \vartheta(D_x + \eta_x + 1)`$。$`\iota_x`$ は
Wilken の段のずらし（APAL 145, 130–161, Def 7.1）。

- **SHIFT**（引用。査読者が場所と仮定を確かめた）。[FANFREE-ja.md](FANFREE-ja.md) §10.2 で未解決だった段のずらしは Wilken の論文にある：Def 7.1、Lemma 7.2、Cor 7.3、
  Lemma 7.4、7.8、7.9。**補題 SUBST**（証明済み）：$`\varepsilon`$ 数 $`g \lt h`$ について、区域の移し $`\sigma_{g\to h}`$ は Wilken の項での置き換え $`g := h`$ で、
  $`\iota`$、$`x \mapsto x^+`$、局所化と交換する。（査読者：$`\omega^z`$ について引用した補題は違うものだが、主張は Lemma 4.2 と SUBST (b) で成り立つ。
  また SUBST (c) は $`x = g`$ で使われており、その場合は Lemma 5.5 で成り立つので書き足すべき。）
- **届く先**（定義）。$`\rho(x)`$ は Wilken の本当の $`R_1^+`$ の届く先（Wilken, APAL 145, 162–175, Def 4.1。[PSS/POR.md](../../BMS/PoR/PSS/POR.md) §3.3 の
  畳み込みと同じ）で、最後の部分を符号全体 $`\Lambda_x = \iota_x(D_x)\cdot 2 + \eta_x`$ に替え、畳み込みのあとに足したもの。Wilken 自身の届く先は、要る意味で
  単調でない：$`g = \varepsilon_\omega`$、$`h = \varepsilon_{\omega+1}`$ で $`\sigma(\mathrm{lh}(g)) = h\cdot 2 + 1 \gt \mathrm{lh}(h) = h\cdot 2`$。
- **補題 R+、LOC、LAM、UNIF、MON**（証明済み）。$`\rho(x) \lt x^+`$。$`\upsilon_1`$ より下のすべての順序数で、届く先の区間は入れ子か交わらない。$`\rho`$ は $`\sigma`$ と
  交換する。$`g \lt h`$ と $`a_g \lt a_h`$ から $`\sigma_{g\to h}(\rho(g)) \lt \rho(h)`$。だから [FANFREE-ja.md](FANFREE-ja.md) §10.2 の場合 EQUAL-TOP は起きない。（査読者：MON のいちばん難しい場合は
  本当に起きる。たとえば $`g = \vartheta_0(\vartheta_1(\vartheta_2(\Omega_3)))`$。）
- **FIN、PAT-U、HOST-U、GROUP、CODE-U**（証明済み）。符号は有限の、L1p の無い扇の無い RF パターン。新しい $`\varepsilon`$ 数の添字はその区域と
  いっしょに置き、区域の点もそれぞれの区域といっしょに再帰的に置き、どのまとまりもその宿主で R1 によって映す。
- **定理 IDX-U**（証明済み）。$`\omega \le \alpha' \lt \alpha \lt \upsilon_1`$ で $`N(\alpha') \ll N(\alpha)`$。HOST2（[FANFREE-ja.md](FANFREE-ja.md) §7.2）と合わせて $`\iota(\mathrm{CH}_2) \ge \upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$
  （前は $`B`$）。
- **定理 IDX-REF**（証明済み。ただし 1 つの段 STEP-IN は略図だけで、論文の §5 を「相対化したもの」と 8 行で書き、新しい 3 つの場合を書いていない。
  査読者はその 3 つを手で確かめ、成り立つが、相対化した置き方は一度も実行していない）。添字の族 $`[\omega, \upsilon_1)`$ のあとに、各
  $`\beta \lt \upsilon_1`$ ごとに $`[\upsilon_1, \upsilon_2)`$ の写しを 1 つずつ並べた族（基 $`\psi_{\Omega_1}(\Omega_\beta)`$ で読む）は順序型 $`\upsilon_2\cdot\upsilon_1`$ で、その符号は
  $`\ll`$ で増える（極限では [FANFREE-ja.md](FANFREE-ja.md) §7.2 の補題 REF、新しい補題 UNIV-P と BRIDGE）。だから $`\iota(\mathrm{CH}_2) \ge \upsilon_2\cdot\upsilon_1`$。
- **数えない**：ふくらませた届く先が必要だという論文の注意。Wilken の届く先での失敗が示すのは、この置き方の計画がそれでは壊れることだけ。
- **未証明**：論文の言うとおり $`\iota(\mathrm{CH}_2) \ge \theta_0`$。穴：入れ子の参照（それは $`\psi_{\Omega_1}(\Omega_{\Omega_1}) \lt \theta_0`$ より下にとどまる）と、そのあとの
  $`\Omega`$ の段のブロックの文法。

## 3. $`\Phi_3`$ の形：$`t = 1`$ の段のための周期的な記号

記号は [FANFREE-ja.md](FANFREE-ja.md) §7.1 と [FANFREE-ja.md](FANFREE-ja.md) §10.1 と同じ。$`P_m`$ は $`A[m]`$ での悪い根 $`R`$ の部分木、$`H`$ は穴を 1 つ持つ $`A[1]`$ での $`R`$ の部分木で、$`P_m = H[P_{m-1}]`$。定理は
$`\Phi_3`$ の文章の定義についてのもので、すべて $`R_2^C`$ での話。

- **補題 SEQ**（証明済み）。ふつうの列と、長さが $`j`$ について 1 次で伸びる「切片」からなる列の語を比べる手続き。どの $`j \ge J_0`$ でも成り立つ順序を
  返すか、そのような順序は無いと報告する。（査読者：跳びの規則の枝の 1 つは決して走らない。）
- **補題 SYM-P**（[FANFREE-ja.md](FANFREE-ja.md) §10.1 の補題 SYM と同じく、プログラムの Python の意味についての紙の議論として証明済み）。記号 $`Z`$ は、すべての $`j \ge J_0`$ の
  $`P_j`$ を一度に表す。その子は $`P_m = H[P_{m-1}]`$ で必要なときに正確に開く。$`Z`$ でのプログラムの実行が走り終われば、どの $`j \ge J_0`$ の $`\Phi_3`$ も
  分かる。これで [FANFREE-ja.md](FANFREE-ja.md) §10.1 の $`t = 1`$ の ROOT の障害が取れた。（査読者：証明はプログラムの同一性の検査のうち 3 つを見落とし、実行が項の
  しまい方や呼ぶ順序によらないことを証明無しに使う。これは確かめただけで、標本の 3,166 個の行列を 3 通りに作って違いは 0。）
- **定理 PER**（SYM-P のもとで証明済み）。$`t = 1`$ の ROOT の 302 個の行列のうち 292 個で、どの $`n`$ でも $`\Phi_3(A[n])`$ の形が分かる。段の幅は 1 か 2
  で、上の部分は決まっている。
- **定理 SELF-CHAIN-C**（証明済み。1 つの式の添字を、査読者が $`\beta(P_{n-s})`$ に直す）。そのうち 285 個で、どの $`n`$ でも FS$`^+`$。[FANFREE-ja.md](FANFREE-ja.md) §10.1 で小さい $`n`$ で
  確かめた条件のもとでだけだった 58 個を含む。
- **定理 IX-PER、IX-CORE、SUM-CORE**（証明済み）。$`t = 1`$ の部分 I と III で：組の項の添字（新しく 127 個）と、$`R`$ での核（新しく 94 個）。SUM で
  新しく 62 個。（査読者：IX-PER の記号の検査が示すのは、添字の部分が主張する集合に含まれることだけで、等しいことではない。FS$`^+`$ に要るのは
  この包含だけで、等しいことは $`n \le 9`$ で確かめた。）
- **標本の上で証明された部分**（[FANFREE-ja.md](FANFREE-ja.md) §1 の 3,166 個の行列）：

| 部分 | 行列 | すべての $`n`$ で証明済み | LOW のもとで | 小さい $`n`$ で確かめた条件のもとで | 未解決 |
|---|---|---|---|---|---|
| I | 581 | 277 | 21 | 0 | 283 |
| SUM | 603 | 480 | 0 | 7 | 116 |
| ROOT | 635 | 491 | 0 | 0 | 144 |
| III | 1,347 | 194 | 0 | 0 | 1,153 |
| 全部 | 3,166 | 1,442（前は 874） | 21 | 7 | 1,696 |

- [FANFREE-ja.md](FANFREE-ja.md) §10.1 の一覧から漏れた 267 個のうち、37 個が今は証明済み（どれも $`t = 1`$ で 3 行の部分項を持つ部分 III）。
- **未解決**：SRO より下の UNIF-FS。証明されていない 1,724 個は次の類に分かれる（数が合うことは査読者が確かめた）：

| 類 | 行列 | 未解決の理由 |
|---|---|---|
| $`t = 0`$、悪い根が根の列でない | 882 | 写しが兄弟になる。周期的な部分項でなく、子のくり返し |
| $`t = 2`$ | 460 | $`n`$ とともに深くなる鎖。新しい定理が要る |
| $`t = 1`$、悪い根が $`\Omega`$ の段の構造の中（III） | 201 | 実行が $`Z`$ の中へ降りる。像の記号が要る（概略だけ） |
| ほかの $`t = 1`$ の部分 I と III | 140 | 実行が $`Z`$ の中へ降りる、$`n = 0`$ で写像が無い、または核の節点が雛形より上にある |
| ROOT、$`t = 1`$ | 17 | 7 個は [FANFREE-ja.md](FANFREE-ja.md) §7.1 の基の障害（基のブロックの節点が最初のブロックに届く）に当たる。10 個は PER が成り立たない |
| SUM、$`t = 1`$ | 24 | 13 個は変わる和の項が決まった項と入り混じる。11 個は部分 III の核を持つ |

## 4. 直接の $`\Sigma_2`$ の議論による $`\nu_C = \nu_S`$

記号は [COVER-ja.md](COVER-ja.md) §6.3 と [FANFREE-ja.md](FANFREE-ja.md) §10.3 と同じ：$`x = x_2`$、$`\nu = \nu_C`$、$`U_2`$、$`S_n`$、$`S_\omega`$。$`R`$ は $`\nu_C`$ より下で $`R_2^C`$ と $`R_2^S`$ が
共有する構造。有限集合の写しが **正確** とは、増加する全単射が $`0, +, \le, \le_1, \le_2`$ を両方向に保つこと（同型）で、前向きだけ（被覆）ではない。

- **ET**（証明済み。ただし新しくない：査読者によると [README-ja.md](README-ja.md) §3 の定理 T2 と同じで、それは既に「同値」。数えない）。
  $`x \le_2^S \nu`$ は次と同じ：どの有限の $`p \subset x`$、$`Y \subset S_\omega`$、$`k`$ にも、$`p`$ の上で同じ図式を持つ $`\tilde Y \subset x`$ があり、$`R|x`$ での $`\tilde Y`$ の
  どの $`k`$ 点の拡張も $`R|\nu`$ で $`Y`$ の上に実現される。[FANFREE-ja.md](FANFREE-ja.md) §10.3 の長いやり直しの点の障害 NEED-C は $`k = 5`$ からこれに当てはまる（ET-LONG、証明済み）。
- **HULL**（証明済み）。どの有限の $`p`$、$`Y`$ にも、$`R|x`$ の $`\Sigma_1`$ 初等的な部分構造 $`M`$ と、$`p`$ を動かさず $`Y \subseteq j[M]`$ となる埋め込み
  $`j : M \to R`$ があれば、$`x \le_2^S \nu`$。だから LBC から Wilken 2020, Prop 21.11 を使わずに直接 $`\Sigma_2`$ が出る。（査読者：全体の LBC の写像が
  この性質を持つという注意は確かめていない。）
- **DOWN-EX と UP-EX**（証明済み。Carlson 2009 の Def 9.4、10.1、13.10 と Thm 14.10、14.11 の引用は仮定まで合っている）。$`x`$ と $`\nu`$ を含む
  $`R_2^C`$ のどの isominimal な集合の上でも、Carlson の 2 つの 2-反映の規則は、被覆だけでなく正確な写しを与える：$`x`$ の下（下向き）と、
  $`\nu`$ のすぐ下で集合の残りより上（上向き）。これは、[COVER-ja.md](COVER-ja.md) §6.3 の 7 回目の論文の「被覆としてだけ」という注意を正す。
- **L17-EX**（(2) は証明済み、(1) は書かれたままでは未証明）。(2)：$`Y \subset S_\omega`$ について、$`x`$ の下に共終的に、与えられた $`X \subset x`$ の上の
  $`Y`$ の正確な写し $`\tilde Y`$ があり、$`\tilde y \le_1 x`$ は $`y \le_1 \nu`$ と同じ。(1)「$`x`$ の下に共終的に実現される $`X`$ の上のどのパターンも、$`\nu`$ の下に
  共終的に実現される」は写しが閉じていることが要り、同型からはそれが出ない（査読者の例：$`X = \emptyset`$、$`Z = \{\omega\}`$、$`Z' = \{\omega+1\}`$）。その
  仮定を足せば成り立ち、使う所ではそれで足りる。これらは Wilken 2021, Lemma 1.7 の $`(x, \nu)`$ での正確な形で、被覆の形は知られていた。
- **TOP**（証明済み。査読者はどの種類の関係も確かめた）。$`\tilde Y`$ を $`Y`$ の下向きの写しとする。$`R|x`$ での $`p \cup \tilde Y`$ の拡張で、$`\tilde Y`$ より上にあり、
  和 $`z + \tilde y`$（$`\tilde y \in \tilde Y`$）を含まないものは、どれも $`R|\nu`$ で $`p \cup Y`$ の上に同じ図式で実現される。これは NEED-C のパターンを含む：
  上向きの規則が、その長いやり直しの点を $`S_\omega`$ に正確に、届く先の値を使わずに与える。（査読者：「写しより上のどの長いやり直しのパターン
  も」はこのような拡張についてだけ成り立つ。）
- **DECOUPLE**（証明済み）。$`x`$ の写し $`\tilde x = \upsilon^2_m`$ より下の点は、$`Y`$ に対するのとちょうど同じように $`\tilde Y`$ に $`\le`$、$`\le_1`$、$`\le_2`$ で関係する
  （補題 CUT）。$`\tilde x`$ と $`\max\tilde Y`$ の間の点は、写しより上の点と $`\le_1`$ でも $`\le_2`$ でも関係しない。
- **未証明**（止める点）：「(LOC) と (TR) から $`\nu_C = \nu_S`$」。(LOC) は有限の包 $`[\tilde x, \max\tilde Y]`$ の局所的な基の取り替え、(TR) は写しより上の $`z`$ と
  包の中の $`v`$ の和 $`z + v`$ を扱う。判定法は拡張より先に $`\tilde Y`$ を決めるので、拡張は isominimal な集合の外の点 $`t \lt \tilde x`$ を含みうる。すると
  $`z + t`$ のような和はどの道具にも入らない（例：$`\{t, z, z + t\}`$ で、$`z \le_1 z + t`$ を移さなければならない）。正しい残りは、任意の有限集合
  $`T \lt \tilde x`$ を止めたままの (LOC) と (TR)。だから GHOST-SHAPE の読み「幽霊は (LOC) か (TR) を使う」も証明されていない。文字どおりの命題は
  証明済みだが自明（数えない）。
- **未解決**：$`\nu_C = \nu_S`$。論文は $`R|x`$ と $`R|\nu`$ を分ける具体的な $`\Sigma_2`$ の文を見つけていない。

## 5. 11 回目のあとの状況

- $`R_2^C`$ での Wilken の主張：両方の半分が $`[0, \rho_{\Lambda_{\mathrm{fp}}+\omega^2})`$ で成り立ち、そこの届く先は閉じた形（§1）。$`\nu_C`$ より下の GEN の範囲では、
  やり直しの点の Klammer の形がその名前から読める（KV-NAMES）。$`\Theta_1 = H(\theta)`$ は包の一致 (H2a) と (H2b) に帰着した。
- $`\theta_0`$ より下の下界の計画：SRO より下の段は、標本の 3,166 個の行列のうち 1,442 個ですべての $`n`$ で証明済み（§3）。素の符号は $`[\omega, \upsilon_1)`$ と
  1 段の参照の上で順序が証明され、だから $`\iota(\mathrm{CH}_2) \ge \upsilon_2\cdot\upsilon_1`$（§2）。
- 最初の到達不能基数：$`H_m`$ は未解決。$`\iota(\mathrm{CH}_2) \ge \theta_0`$ から出る。
- 上からの評価：どの $`\iota(\mathrm{CH}_k)`$、$`m_F`$、$`x_F`$、$`C^*_3`$、$`\nu_C`$ にも InaccPsi による評価は証明されていない。
- $`\nu_C = \nu_S`$：isominimal な集合の上では 2-反映の写しは正確で、写しより上のどの拡張も合わせられる（TOP）。残るのは、写しより下の有限集合を
  止めたままの (LOC) と (TR)。

## 6. 11 回目の確認

どの実行も 60 秒未満。どれも証明ではない。証明書は再生されたものだけを数える。

- 名前（§1）。名前を付けた 25 個の点は標準形で狭義に増加する（Python と Lean の試験のファイルで。緑。査読者の再実行はバイト単位で同じで緑）。
  $`\psi_{\Omega_2}`$ は標本の上で PSI2 のとおりに振る舞う。基 $`\Omega_1`$、$`\Omega_2`$、$`\Omega_3`$ での UNIF-G：48,180 回の比較で食い違い 0（査読者：基数の基でだけで、
  NAME-OFFSET-G は可算な $`\upsilon`$ 点で使う。証明はその場合を含むが、確認は含まない）。$`\psi_{\Omega_2}(\Omega_2)`$ より下の 197 個のずれ：順序の付いた組
  38,612 個で食い違い 0。査読者自身の PSI2 の試し（$`\varphi`$ の項 33,436 個などを含む）：反例無し。VEB-THETA と EXACT-G は Wilken の系についてのもので、
  ここにはその実装が無いので試していない。
- 符号（§2）。実現した順序での置き方：21,125 段、そのうち $`B`$ より先が 20,159 段、区域は深さ 3 まで入れ子。MON と UNIF を 6,968 組、LAM を
  16,846 組、符号 20,712 個。変えた規則はどれも見つかる（畳み込み無し。Wilken の届く先は 6,299 段のうち 1,730 段で失敗。2 つ目の宿主）。予想どおりの
  向きの証明書 12 個はどれも再生できる。逆向きの探索 2 回では何も無い。時間切れの実行が 1 つあり、数えない。査読者：MON を 7,180 + 831 + 12,185 組、
  UNIF を 81,965 点、LAM を 92,306 回と LOC を 197,192 回、新しい種での置き方（2,629 段）：失敗 0。（査読者：どの実行を止めたかを論文は 2 通りに
  書いており、開発中の 1 つの実行には出力のファイルが無い。）
- 形（§3）。記号の雛形は、受け入れたどの行列（ROOT 285 個、IX-PER 249 個、IX-CORE 245 個）でも、$`j`$ の 4 つの値で具体的な $`\Phi_3`$ と同じ。標本の外の
  乱数の行列で受け入れた 603 個はどれも正しい。査読者：SEQ を語の組 60,000 個（決まったのは 53,171 個、そのうち跳びで 10,616 個）で、間違い 0。PER と
  SELF-CHAIN-C をより高い段で（幅 1 で $`n`$ が 11 まで、幅 2 で 14 まで）。IX-PER と IX-CORE を $`n = 9`$ まで。3,166 個の行列を 3 通りに作って違い 0。
- $`\Sigma_2`$（§4）。論文は何も実行していない。査読者は TOP で使う和についての事実を $`\omega^\omega`$ より下の乱数の 93,411 例で確かめ、失敗 0。

## 7. 未解決

- 最初の到達不能基数：$`H_m`$（言い換えると、ある $`\iota(\mathrm{CH}_k) \ge \theta_0`$。$`\iota(\mathrm{CH}_2) \ge \theta_0`$ で足り、それは、値が L1p の無いパターンで、どの段でも
  $`\nu(s) \ll \nu(t)`$ となる $`D`$ 全体の上の写像 $`\nu`$ から出る）。§3 の未解決の類での SRO より下の UNIF-FS。入れ子の参照を持つ符号と、
  $`\Omega`$ の段のブロックの文法（§2）。$`\iota(A_n) \ge |\tau_n|`$。
- 上からの評価：$`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$、または $`\nu_C`$ のどれかの InaccPsi による評価。STEP-CH（$`\Phi`$ で閉じた類の上で、
  崩壊の引数が $`I_0`$ より下）。REL-SHARP。(HQ)。
- $`\Lambda_{\mathrm{fp}}`$ より先の名前とずれ：$`\psi_{\Omega_2}(\Omega_2)`$ より先での (H2a) と (H2b)（$`\Theta_1 = H(\theta)`$ が出る）。$`\Theta_A`$、$`\Theta_\delta`$、$`\Theta_{d\omega}`$、$`\Lambda^*`$、
  $`\nu_P`$ の名前。$`\nu_C \lt \upsilon^*`$ かどうか。
- $`\nu_C = \nu_S`$：写しより下の有限集合を止めたままの (LOC) と (TR)（§4）。(PROF)。$`k`$ の不動点の極限での届く先。$`[x, x^\#)`$ より先の
  $`Y \subset S_\omega`$。
- [COVER-ja.md](COVER-ja.md) §9 の残り。
