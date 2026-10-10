[← Back](README-ja.md) | [English](SHIFT10.md) | [Japanese](SHIFT10-ja.md)

# $`R_2^+`$ の 38 回目：1 つ上の窓の規則、骨組みの最初の長いやり直し、$`Z^{\mathrm{LL}}`$ までの主張、帰納法としての判定、印のついた源

このページは [SHIFT9-ja.md](SHIFT9-ja.md) の続き（そこの §3 が 37 回目）。§1 が 38 回目。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。致命的な点か進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことか目標そのものの言い直しにすぎないと言った結果は、進みとして数えない。

## 1. 38 回目

論文は 3 本（2026-10）、どれも査読 1 回：1 つ上の窓の規則と骨組みの最初の長いやり直しの論文（§1.1）、(E)、$`\delta''_1`$ の切片、帰納法としての判定の論文（§1.2）、素の符号の論文
（§1.3）。この節の結果は、回数を書いていなければ査読 1 回。主張の $`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$ から $`Z^\varepsilon`$（下で定める）までの段階は、$`G''(\omega+1)`$ より上の符号の 2 つの
違う読みにより、はじめの 2 本の論文で別々に証明されたので **査読 2 回**。$`R_2^S`$ での主張の $`Z^\Gamma`$ から $`Z^\varepsilon`$ までの段階も同じ。[SHIFT9-ja.md](SHIFT9-ja.md) §3.1、§3.2、§3.3 の査読の細かい
点は 3 本の論文が反映し、その査読者がどの直しも確かめた（**査読 2 回**。新しい点があるところは書く）。どの論文も Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を
使わない（査読者が確かめた）。引く論文：§1.1 は査読済みの段階のほかに Wilken "Σ₁-elementarity and Skolem hull operators"（APAL 145, 2007。L.2.1、Def 4.1、Thm 2.2）、Carlson 2009（Def 5.3、L.5.5、
L.5.7）、Wilken の "A glimpse of Σ₃-elementarity"（L.21.10）。§1.2 は Carlson–Wilken "Tracking chains of Σ₂-elementarity" [CW12b]、https://www.sciencedirect.com/science/article/pii/S0168007211001199
（Prop 7.1、Prop 7.4、そのあとの注意、L.7.5、型として読んだ Thm 7.9 の証明）と Carlson 2009（Def 5.3、Def 5.4、L.5.5、L.5.7）。§1.3 の証明済みの段階はどの論文も使わず、FRAG も使わない。
Lean のファイルは足していない：§1.1 と §1.2 の順序数の入力は項を比べるだけの Lean のファイルで確かめた（`#eval`、定理は無い。緑で Python と同じ出力。査読者の確かめ直しでも同じ）。§1.3 の
査読者は、直した PER-KIND の降下を別の Lean のファイルで確かめた（緑、標準の公理だけ、`sorry` 無し）。これらは確かめた扱い。段の番号は [SHIFT8-ja.md](SHIFT8-ja.md) と同じ（論文より 1 つ上）。
「FRAG のもと」もそこと同じ。

記号（[SHIFT9-ja.md](SHIFT9-ja.md) §3 と同じ）：$`L(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$、$`\theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2)`$、$`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$。今はどの順序数 $`\zeta`$ でも
定める（$`\theta'_2\cdot\zeta`$ は $`\zeta`$ の Cantor 標準形の項 $`\omega^a`$ ごとの $`\omega^{\theta'_2+a}`$ の和）。だから $`G''(\omega^2) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2})`$。骨組みのやり直し $`b = L(\lambda'')`$ について：
$`\tau''_j = L(\lambda''+\omega\cdot j)`$、$`\delta''_j = L(\lambda''+\omega\cdot j+1)`$。そのブロックは $`(b, \delta''_1]`$ と $`(\delta''_j, \delta''_{j+1}]`$、$`\delta''_j`$ の区間は $`[\delta''_j, L(\lambda''+\omega\cdot j+2))`$。
この回の 2 つの最前線は

```math
Z^{\mathrm{LL}} = L(\theta'_2\cdot\omega^2+\omega^{G''(\omega^2)^2}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{\omega^{G''(\omega^2)\cdot 2}}),
```

```math
Z^\varepsilon = \varphi(\omega, \delta^\varepsilon+1),\qquad \delta^\varepsilon = L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega}+\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+1} + \theta'_2 + \varepsilon_{G''(\omega+1)+\omega} + \omega^{P'+1} + P').
```

ここで $`\delta^\varepsilon`$ はやり直し $`L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega})`$（符号は $`\varepsilon_{G''(\omega+1)+\omega}`$）の点 $`\delta''_1`$ で、$`Z^\varepsilon \lt L(\theta'_2\cdot\omega^2) \lt Z^{\mathrm{LL}}`$。

### 1.1 1 つ上の窓の規則と最初の長いやり直し：FRAG のもとで $`Z^{\mathrm{LL}}`$ までの主張

- **[SHIFT9-ja.md](SHIFT9-ja.md) §3.1 の査読の直し**（m1–m6。**査読 2 回**）と、そこの §3.2 の査読の記号 $`\Phi^W_0 := \Omega_1`$（m4）。これで、そこの §3.2 の下ろす写像は、段の写像 $`\mathrm{Tr}_0`$ を
  $`\Gamma`$ の段に制限したものになる。査読者：m1 の一般の形（TAIL-DOM、「どの尾でも符号の定数は定義域に入る」）は、符号の可算の定数より下の尾では偽（反例）で、それより上の尾では真。
  どの証明もそれだけを使う（新しい細かい点 m2。査読 1 回）。
- **TIER$`_\zeta`$ と READ″$`_\zeta`$**（証明済み、FRAG 無し。読みは移しで）。$`\theta'_2\cdot n`$ を $`\theta'_2\cdot\zeta`$ に替えた段の写像は、どの可算の $`\zeta`$ でも、また $`\zeta = \Omega_1`$ でも、$`[\Omega_1, P')`$ の符号から
  $`[G''(\zeta), G''(\zeta+1))`$ の符号の上への順序同型。査読者：「どの順序数 $`\zeta`$ でも」は偽。$`\zeta = P_3 = \psi_{\Omega_2}(\Omega_\omega\cdot 3)`$ などの非可算の $`\zeta`$ では項 $`G''(\zeta)`$ が標準形でない (m1)。
  使うのは可算の $`\zeta`$ と $`\Omega_1`$ だけ。どの点 $`b = L(\lambda'')`$ と、どの可算の $`\zeta \lt b`$ でも：$`o_b(G''(\zeta)) = L(\lambda''+1+\zeta)`$。$`b`$ での定義域に $`G''(\zeta)`$ が入る可算の $`\zeta`$ は
  ちょうど $`b`$ より下のもの。$`G''(\Omega_1)`$ は $`L(\lambda''+b)`$ を読む。[SHIFT9-ja.md](SHIFT9-ja.md) §3.1 の定義域の判定は $`Z^{\mathrm{LL}}`$ の添字まで成り立つ。
- **区間全体の閉じた点**（ROOT″、LC-FORM″、ENUM″、ROOT-LOC″、TRANS-K″。移しで証明済み、FRAG 無し）。$`d = \delta''_j = L(e)`$ について、$`y \in [d, L(e+1))`$ が $`d`$ について閉じているとは、
  どの $`\alpha \in (d, y]`$ でも $`\mathrm{lh}(\alpha) \le y`$ のこと（$`\mathrm{lh}`$ は $`R_2^S`$ での届く先）。$`\alpha_x`$ を $`\alpha \le_1 x`$ となる最小の $`\alpha \in (d, x]`$ とする。すると

```math
E''_d(c) = c\ \ (c \lt d\cdot\omega),\qquad E''_d(c) = \mathrm{lh}(\alpha_{\mathrm{lt}(c)}) + (-\alpha_{\mathrm{lt}(c)} + c)\ \ (c \ge d\cdot\omega)
```

  は $`[d, L(e+1))`$ からこの閉じた点の上への順序同型。これは [SHIFT4-ja.md](SHIFT4-ja.md) §2.1 の ENUM を、1 つの切片でなく区間全体で述べたもの。査読者：その証明が使うのは $`\le_1`$ の区間の
  性質と持続の性質だけで、それは区間で成り立つ。根 $`\alpha_x`$ は $`x`$ より下の最後の $`\upsilon`$ の点の前置の点か、その局所化の中にある（ROOT-LOC″）。だから区間でのどの基の取りかえも $`E''_d`$ と
  入れ替わる（TRANS-K″）。
- **区域全体での留め**（INDEX″、L-PIN″、FAR-PIN″$`^{\mathrm{reg}}`$、PAT-CL″、BLOCK″$`^b`$。移しで証明済み、FRAG のもと）。著者は INDEX″ の初めの稿を直した（区域をまたぐ長いやり直しの像は
  自分の区域に留まるとは限らない）。書き直した形は証明済み。査読者：集合が出会った最後のブロックの点 $`L`$ の区間と交わるとき、L-PIN″ と FAR-PIN″ にはパターンに次のブロックが要るので、
  そこでは書いたままでは証明されていない。どの使い方もその場合を避ける (m3)。
- **定理 EXACT-CL″\*、1 つ上の窓の規則**（移しで証明済み、FRAG のもと。$`\kappa_0`$ は符号の可算の定数より上にとる、m2）。$`I''_1 = [0, G''(\omega+2))`$、$`j \ge 2`$ で
  $`I''_j = [G''(\omega\cdot(j-1)+2), G''(\omega\cdot j+2))`$、$`\mathrm{Lo}_1 = 0`$、$`\mathrm{Lo}_j = L(\lambda''+\omega\cdot(j-1)+2)`$ とする。符号（または π の符号）$`c`$ が $`I''_j`$ にある骨組みのどのやり直し $`L(\lambda'')`$ でも

```math
r(L(\lambda'')) = E''_{\delta''_j}(\delta''_j + (-\mathrm{Lo}_j + o_b(c))).
```

  だから $`G''(\omega^2)`$ より下のどの符号もちょうどの届く先を持ち、それは $`\delta''_j`$ の区間の中にある。符号 $`G''(\omega+2)`$ は $`\delta''_2`$ に届く。**NO-NAIVE″**：符号 $`\omega^{G''(\omega+1)+\omega}`$ での
  届く先は $`\omega^{\delta''_1+\omega}+1`$ で、$`\delta''_1 + o_b(c)`$ ではない。[SHIFT9-ja.md](SHIFT9-ja.md) §3.1 の概略（$`G''(\omega+1)\cdot\omega`$ までの符号）は $`j = 1`$、$`c \lt G''(\omega+1)\cdot\omega`$ の場合。定理 C$`^\Lambda`$：
  主張は $`R_2^C`$ で $`[0, L(\theta'_2\cdot\omega^2)]`$、$`L(\theta'_2\cdot\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2})`$ で、両方の半分とも成り立つ。
- **最初の長いやり直し**（LONG″-$`G''(\omega^2)`$、PIN-ALL″、TOP-REG-FAR″、LB″、EXACT-LONG-CL″\*、CROSSED″。移しで証明済み、FRAG のもと）。最初の長いやり直し $`L(\theta'_2\cdot\omega^2)`$（符号は
  $`G''(\omega^2)`$）は $`\delta''_1(\lambda''+\omega^2)+1`$ に届く：

```math
r(L(\theta'_2\cdot\omega^2)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{P'+2} + \omega^{P'+1} + P') + 1.
```

  $`D, m_0 \lt G''(\omega^2)`$ で符号 $`c = G''(\omega^2)\cdot D + m_0`$、$`\nu = L(\lambda''+\omega^2\cdot o_b(D))`$ のとき：$`m_0 \lt P'`$ なら $`r(L(\lambda'')) = r(\nu) + o_\nu(m_0)`$、$`m_0 \ge P'`$ なら $`\nu`$ での窓の
  規則。だから $`G''(\omega^2)^2`$ より下のどの符号もちょうどの届く先を持つ。CROSSED″：長い届く先がまたぐ区域は骨組みを保つ。査読者：1 つの引用はその仮定の外で使われているが、結論は同じ
  補題のほかの部分で成り立つ (m4)。EXACT-LONG-CL″\* と CROSSED″ の証明は位置をまたいで互いに頼るので、帰納法は符号でなく右の上限に沿って進めるべきで、前の査読済みの証明と同じ。
  そうすれば閉じる (m5)。
- **定理 C$`^{\mathrm{LL}}`$ と新しい最前線**（移しで証明済み、FRAG のもと）。$`Z^{\mathrm{LL}}`$ より下ではどのやり直しもちょうどの届く先を持ち、扇の頂点も 3 重の入れ子も無い。だから $`\beta_0 \gt Z^{\mathrm{LL}}`$、
  $`T_3^C \gt Z^{\mathrm{LL}}`$、**$`R_2^C`$ での Wilken の主張は $`[0, Z^{\mathrm{LL}}]`$ で両方の半分とも成り立ち**、**$`[0, Z^{\mathrm{LL}}) \subseteq \mathrm{Core}(R_2^S)`$ で、だから $`R_2^S`$ での主張は $`[0, Z^{\mathrm{LL}})`$ で成り立つ**
  （NO-GAP の議論による、[SHIFT9-ja.md](SHIFT9-ja.md) §3.2）。これは $`R_2^S`$ の最前線 $`Z^\Gamma`$ を越える。1 つの文（「固さの一覧はそのまま成り立つ」）は確かめておらず、要らない：注意 (m6)。
  CODES‴（証明済み）：$`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ より下の骨組みのどのやり直しも、$`\Omega_2`$ より下の符号か $`P_3`$ より下の π の符号を持つ。言い回し (m7)。
- **未証明**。CROSS″（符号が $`G''(\zeta)`$ 以上、$`\omega^2 \le \zeta \lt b`$ のときの下からの評価 $`r(b) \ge L(\lambda''+\zeta)`$）：概略。未解決：符号が $`G''(\omega^2)^2`$ 以上のちょうどの届く先、$`\omega^2`$ より
  先の段 $`G''(\zeta)`$ を長い符号として、$`G''(\Omega_1)`$ からの符号、1 つ上の着地の計算、1 つ上の CAP-0 と NOT-LOW（最初の試しの場合は $`L(\Omega_3)`$）、$`\nu_3`$ のための 1 つ上の CROSS-LIM、FRAG、
  SHIFT。$`T_3 \le \nu_3`$ は主張しない。分かっていること：$`T_3^C \gt Z^{\mathrm{LL}}`$。

### 1.2 (E)：$`\delta''_1`$ の切片、帰納法としての判定、型 F

言葉は [SHIFT9-ja.md](SHIFT9-ja.md) §1.2、§2.2、§3.2 のもの。「Pred₁(α)」は $`\alpha`$ の $`\le_1`$ の前の点の集合。「判定」は [CW12b] Prop 7.4 のもの。

- **[SHIFT9-ja.md](SHIFT9-ja.md) §3.2 の査読の直し**（m1–m9。**査読 2 回**）。F-REDUCE は今は型 N、部分型 (N0)、(N1)、(N2) と言う (m1)。一般の判定の補題の結論は
  $`\beta_0 \gt \min(b, \kappa_C)`$ (m2)。Lean のファイルは今は $`Z^\Gamma`$ も含む (m3)。$`\Phi^W_0 := \Omega_1`$ (m4)。「判定は (E) より真に強い」は取り下げ、その補題は言い直しと札を付けた (m5)。
  m6、m7 の引用を直した。評価の鎖は $`\nu_3`$ でなく $`T_3^C`$ を使う (m8)。1 つの札 (m9)。
- **NO-GAP$`^R`$**（移しで証明済み、FRAG のもと）。$`\beta_0 \gt Z_R`$、$`[0, Z_R) \subseteq \mathrm{Core}(R_2^S)`$ で、そこで $`f`$ は恒等。ここで $`Z_R = L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$。
- **SEG-GAP**（移しで証明済み、FRAG 無し）。最初のブロックが分かっている計算のどの基の点 $`b = L(\lambda'')`$ と $`d = \delta''_1(\lambda'')`$ でも、$`(d, \varphi(\omega, d+1)]`$ のどの点も共終な Pred₁ を
  持たない。だからそこに端を持つ $`\lt_2`$ の組は無く、$`\beta_0`$ と $`T_3^C`$ は $`\varphi(\omega, d+1)`$ より上。査読者：正しいが、引いた結果が与えるもの、つまり $`d`$ より上の極限の添字の次の $`\upsilon`$ の点
  までの同じことに届いていない (m1。査読者の注意で、数えない)。
- **$`\delta''_1`$ の切片**（READ″$`^\varepsilon`$、LH″、CLOSED″、TOP-REG″$`^{\mathrm{seg}}`$。証明済み、読みは移しで）。$`(d, \varepsilon_{d+\omega})`$ で $`R_2^S`$ での届く先は $`R_1^+`$ での Wilken の届く先と等しく、
  $`\mathrm{lh}(\varepsilon_{d+\omega}) = \varepsilon_{d+\omega}\cdot 2 + 1`$。査読者：はじめの部分は $`d`$ の切片全体について SKEL$`^\infty`$（[COVER-ja.md](COVER-ja.md) §5.1）からもう引ける (m2)。「使わない」と書いた注意は
  使われていて、成り立つ (m3)。
- **定理 EXACT-CL″$`^\varepsilon`$**（移しで証明済み、FRAG のもと）。原子 $`G''(\omega+1)`$ の上の符号の読みを $`\sigma_b`$（$`G''(\omega+1) \mapsto \delta''_1`$、$`\varepsilon_{G''(\omega+1)+k} \mapsto \varepsilon_{\delta''_1+k}`$、定数
  $`k \mapsto o_b(k)`$）、$`\mathrm{LHF}''(y) = \mathrm{lh}(\mathrm{lt}(y)) + (-\mathrm{lt}(y) + y)`$（[SHIFT4-ja.md](SHIFT4-ja.md) §1.1 の lh ずらしの 1 つ上）と書く。符号 $`c`$ が $`[G''(\omega+1), \varepsilon_{G''(\omega+1)+\omega})`$ にある
  どのやり直しでも $`r(L(\lambda'')) = \mathrm{LHF}''(\delta''_1 + \sigma_b(c))`$。たとえば符号 $`G''(\omega+1)\cdot\omega`$ は $`\delta''_1\cdot\omega`$ に、符号 $`G''(\omega+1)^2`$ は $`\omega^{\delta''_1\cdot 2} + \delta''_1`$ に、符号
  $`\varepsilon_{G''(\omega+1)+1}`$ は $`\varepsilon_{\delta''_1+1}\cdot 2`$ に届く。符号 $`\varepsilon_{G''(\omega+1)+\omega}`$ は $`\varepsilon_{\delta''_1+\omega}\cdot 2 + 1`$ に届く。これらの届く先は §1.1 と合う（NO-NAIVE″ も含め）ので、2 つの
  証明がある。査読者：ある段階の 1 つの場合分けは誤りだが、議論はそれを使わない (m4)。
- **定理 C$`^E`$**（移しで証明済み、FRAG のもと）。Wilken の主張は $`R_2^C`$ で $`[0, Z^\varepsilon]`$、$`R_2^S`$ で $`[0, Z^\varepsilon)`$ で成り立ち、$`\beta_0 \gt Z^\varepsilon`$、$`T_3^C \gt Z^\varepsilon`$。§1.1 とあわせて
  この段階は **査読 2 回**。査読者：論文自身の区域の記述はもっと多くを与える（おそらくその区域の終わりまで。そこでは証明されていない。m6）。
- **帰納法としての判定**（CRIT-CALCULUS、LOAD、CRIT-IND、LOAD$`^E`$。証明済み）。判定は推移、上限、右端の $`\le_1`$ での制限、SHIFT で閉じている（CC1–CC6。[CW12b] Prop 7.4 のあとの
  注意はこのうち 2 つを証明無しに述べる）。LOAD は [CW12b] Thm 7.9 の証明の載せる段階の抽象的な形。**CRIT-IND**：右端が $`b`$ より下の $`R_2^C`$ のどの $`\lt_2`$ の組も、SHIFT の組、載せた組、
  組の上限のどれかなら、$`\beta_0 \ge \min(b, \kappa_C)`$ で、右端が $`\beta_0`$ 以下のその組で判定が成り立ち（m5：$`R_2^C`$ で使う写しは $`R_2^S`$ の事実）、一様な有限集合の試験はそこで必要。これは
  埋め込みと $`\Sigma_1`$ の型だけについての十分条件で、(E) の言い換えではない（査読者も同意）。**LOAD$`^E`$**（FRAG のもと）：右端が $`Z^\varepsilon`$ 以下のどの組も SHIFT の組。だからそこで判定と、一様な
  試験が必要なことが成り立つ。「どの $`n`$ でも LIFT$`_n`$」は (E) の言い換え：注意で、数えない。
- **型 F**（FAN-UNIFORM、NO-SELF-LOAD。証明済み）。余分な組の左端 $`a`$ について、$`\beta_0`$ より下の $`a`$ の $`R_2^S`$ での後の点には最大のもの $`\delta^*`$ がある（または無い）。分ける $`\Sigma_2`$ の
  証拠はどれも $`[\delta^*, \beta_0)`$ と交わる。F-CRIT-LOW は一般に成り立つ。(N0) と型 F は後の点がある場合で、(N0) では $`\le_1`$ でつながらず、型 F では $`d`$ でつながる。NO-SELF-LOAD：扇の組は
  自分の下の組を通しては載せられない（査読者：右端が $`a`$ の後の点であるどの下の組を通しても、m7）。FAN-LOAD：予想。
- **未証明：帰納法の止まる所**（査読の致命的な点 F-1。1 つの場所の主張だけに対するもので、どの定理もそれに頼らない）。論文は、$`\delta^\varepsilon`$ より上で共終な Pred₁ を持つ最初の点が
  $`\delta^\varepsilon`$ の切片にあるかもしれず、最初に足りない入力はその切片での $`R_2^S`$ の届く先だと言った。偽：NOBAD と INC1（[BREAK-ja.md](BREAK-ja.md) §1）により、そのような点は $`\lambda`$ が極限の
  $`\upsilon_\lambda`$ で、その切片には無い。そしてそこで $`R_2^S`$ は SKEL$`^\infty`$ により $`R_1^+`$ と等しい。帰納法になお要るもの（査読者）：符号が $`\varepsilon_{G''(\omega+1)+\omega}+1`$ 以上の区域の新しい組での
  SHIFT のデータ（そのような最初のやり直しは $`L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega}\cdot\omega)`$）と、(E) のために、扇の頂点と蓋での余分な組 (N0)、型 F、(N1)、(N2) を除くこと。
- **未解決**。(E)。$`x_F^C`$ より上の型 F と (N0)。$`\beta_0 \ge x_F^C`$：予想。

### 1.3 素の符号：印のついた源、容量、段階の道の壁

記号は [SHIFT9-ja.md](SHIFT9-ja.md) §1.3 と §3.3 のもの（単位、物、源、鍵、配置 A と B、宿す場合 F1、鎖の数 $`k`$）。

- **[SHIFT9-ja.md](SHIFT9-ja.md) §3.3 の査読の直し**（m1–m6。査読者が確かめた）。SUCC は、その段階での原子の性質を仮定せずに証明し直した (m1)。1 つの議論は注意と札を付けた (m2)。
  **NO-FIX**（m3。2 つの仮定、固定した部分の凸性と引数の上での閉包、を足せば証明済み）：固定した有限の配置は、それを根より下に含むパターンを宿せない。だから
  [SHIFT9-ja.md](SHIFT9-ja.md) §3.3 の条件つきの結果は取り下げ。
- **印のついた源**（配置 A。UNIV-P$`^m`$、F1$`^m`$、COR HOST$`^m`$、SHAPE$`^m`$。証明済み）。どの物もどの単位も源 $`x' \lt_2 y' \lt s' \lt h'`$、$`s' \le_1 s'\cdot 2`$、$`x', h' \le_1 h'\cdot 4 + m`$ を持つ。
  印 $`m`$ は下の符号の点の和。UNIV-P$`^m`$：そのような源は、自分の源の印がより小さい、添字で符号にしたどの範囲も、どの深さとどの添字でも宿す。F1$`^m`$：客の内側の範囲の印が宿主の源の
  印より下なら、**場合 F1 は宿主の物の中に宿る**。だから置いた印が 3 つの順序の条件 (C1)–(C3) を満たせば、F1 を含めどの合わせも宿る（条件つきの補題）。単位ごとに 2、鎖 4、だからどの深さと
  どの添字でも鎖の数 5。細かい点：1 つの一覧 (m4) と 1 つの上限 (m5)。
- **容量**（KEYCAP、WIT、PER-KIND、STACK。証明済み）。KEYCAP：単位の重さは (C1)–(C3) を満たす。だから順序数の容量はある。PER-KIND：物の値と深さだけで決まる容量は (C1) を満たさない。
  証拠の族 WIT は、$`\Omega_{\omega\cdot 2}`$ から先のどの段階の集合の中でも、どの深さでも場合 F1 を持つ。査読者：証明には 2 つ以上の大きさでの WIT が要る。窓の降下（Lean で確かめた）か、より大きい
  どの大きさでの WIT で直る (m2)。NO-FIX と STACK（深さとともに増える鎖の数は 1 つの部品の系では役に立たない）とあわせて：段階の道は、形を固めた場合、深さで段をつけた容量、深さとともに
  増える鎖の数で、$`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ で止まる。
- **(REP$`^\rho`$) と REP-RANK**（m6、m7 つきで証明済み）。(REP$`^\rho`$)：各単位 $`H`$ の中の、宿す関係を順序づける符号。宿す階数 $`\rho(H)`$（生成された段階では可算）について：そのような符号の値は $`\rho(H)`$ 以上で、
  $`\rho`$ の符号は (REP$`^\rho`$) を与える。**未証明** (m1)：「(REP$`^\rho`$) が成り立つのは $`\rho(H)`$ が $`H`$ の中に符号を持つときに限る」（一方の向きだけ）、「壁は (REP$`^\rho`$) が成り立たないことと同値」（どちらの向きも）、
  前の造りの定義を越えた「段階の道は止まる」。MARKER-SELF（印を、部品の系自身の $`\rho`$ の符号にする）：予想。条件つき（概略）：段階の集合 $`[1, u_m]`$ での (REP$`^\rho`$) は $`\theta_0`$ まで鎖の数 5 を与え、
  だから $`\iota(\mathrm{CH}_5) \ge \theta_0`$ で、最初の扇は到達不能基数を要する。
- **B-1**（配置 B）：直っていない。符号を入れ子の組に置くと鎖が 1 つ増え、やはり鎖の数 5（注意）。
- **素の評価**。新しい評価は無く、失ったものも無い：$`\psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ より下で鎖の数 3、$`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ より下で 4、$`\iota(\mathrm{CH}_5)`$ と $`m_F`$ は
  $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ より上。未解決：(REP$`^\rho`$)、B-1、$`[\psi_{\Omega_1}(\Omega_{\omega\cdot 2}), \theta_0)`$ でのどの素の評価も、$`H_m`$、「最初の扇は到達不能基数を要する」。

### 1.4 38 回目のあとの状態

- $`R_2^C`$ での Wilken の主張：FRAG 無しで $`[0, X_4]`$、そして **FRAG のもとで $`[0, Z^{\mathrm{LL}}]`$、$`Z^{\mathrm{LL}} = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{\omega^{G''(\omega^2)\cdot 2}})`$** で両方の半分とも
  成り立つ（$`Z_R = L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$ までの査読の回数は [SHIFT9-ja.md](SHIFT9-ja.md) §3.4 のとおり。$`Z_R`$ から $`Z^\varepsilon`$ までは査読 2 回で 2 つの証明、§1.1、§1.2。
  $`Z^\varepsilon`$ から $`Z^{\mathrm{LL}}`$ までは査読 1 回、§1.1）。
- $`R_2^S`$ での Wilken の主張：FRAG のもとで $`[0, Z^{\mathrm{LL}})`$（$`[0, Z^\Gamma)`$ は [SHIFT9-ja.md](SHIFT9-ja.md) §3.4 のとおり。$`Z^\Gamma`$ から $`Z^\varepsilon`$ までは査読 2 回で 2 つの証明。$`Z^\varepsilon`$ から先は
  査読 1 回）。FRAG 無しでは $`\upsilon_{\omega^3}`$ まで。
- $`R_2^S`$ と $`R_2^C`$：右端が $`Z^{\mathrm{LL}}`$ 以下のどの関係でも 2 つは一致する（FRAG のもと）。FRAG のもとで $`\beta_0 \ge \sigma_S \ge Z^{\mathrm{LL}}`$。右端が $`Z^\varepsilon`$ 以下のどの組でも [CW12b] の判定と
  一様な試験が必要なことが成り立つ。(E) は未解決で、$`\beta_0`$ の場所は分かっていない。
- 届く先（FRAG のもと）：$`Z^{\mathrm{LL}}`$ より下のどのやり直しでもちょうど。
- **LOW：FRAG のもとで偽**。**LOW$`^\infty`$：FRAG のもとで真**（どちらも査読 1 回。変化なし）。予想 CORE-2 の段階 PIN と LOW：決まっていない（変化なし）。
- $`\theta_0`$ より下の下からの評価の計画：素の評価は [SHIFT9-ja.md](SHIFT9-ja.md) §2.4 のとおり（変化なし）。$`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ より先では、印が正しい順なら場合 F1 は宿り、
  足りないのは (REP$`^\rho`$)（§1.3）。SRO より下の段階：変化なし（3,166 個の標本の行列すべてでどの $`n`$ でも。SRO より下のすべての標準の行列についての一般の命題は未解決）。

### 1.5 38 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。11 回の実行：段 $`\omega\cdot 3+2`$、$`\omega^2`$、$`\omega^2+1`$、$`\omega^3`$、$`\varepsilon_0`$ で段の写像を前向き（段ごとに 220 個の符号と 24,090 組）と後ろ向き（段ごとに 350 個の符号）に、食い違い 0。
  20,388 個の添字で定義域（9,335 個は定義域に入らない）、食い違い 0。$`Z^{\mathrm{LL}}`$ までの名前の鎖とその字面。4 つの基での窓の鎖。遠い添字 44 個中 44 個と長い符号の行き先 24 個中 24 個。
  試験の道具の誤りを 3 つ見つけて直し、論文はそのことを書いている。Lean は緑で Python と同じ。査読者：自前の試験で、届く先の式への反例は無い。非可算の $`\zeta`$ での段 (m1)。5,930 個の
  尾（π の上限の失敗 0）と m2 の反例。15,421 個のやり直しの符号の範囲、失敗 0。3,611 個の意地悪な添字で定義域、食い違い 0。24 個の遠い添字 (m4)。著者の実行と Lean のファイルの
  再実行は同じ出力。
- §1.2。14 回の実行：12,601、14,265、9,670 個の添字で定義域（8,740 個は定義域に入らない）、食い違い 0。行き先 225 個中 225 個。$`Z^\varepsilon`$ までの基での鎖。Lean は緑（今は $`Z^\Gamma`$ も含む）で
  Python と同じ。査読者：2 つの実行の再実行は同じ出力。定数、次のやり直しまでの点の順序、符号の自前の確かめ (m4)。Lean のファイルの再実行は緑。$`R_2^S`$、$`R_2^C`$、届く先、写し、判定は
  計算できない。
- §1.3。証拠の族を 80 個の場合（$`D \le 5`$）で、失敗 0。査読者：実行の再実行は同じ出力。より大きい大きさの 504 個の場合で自前のコード、失敗 0。直した PER-KIND の降下を Lean で。
  実行は宿主の位置を直接は計算しない (m8)。

### 1.6 未解決

- FRAG のもとで $`Z^{\mathrm{LL}}`$ より上の主張（FRAG 無しでは $`X_4`$ より上）、$`R_2^C`$ でも $`R_2^S`$ でも。次は、1 つの区域を越える遠い留めと符号が $`G''(\omega^2)^2`$ 以上のちょうどの届く先、
  CROSS″ と $`G''(\Omega_1)`$ までの段 $`G''(\zeta)`$、$`G''(\Omega_1)`$ からの符号と 1 つ上の着地の計算、$`P_3`$ より下の CAP-0 と NOT-LOW、$`\nu_3`$。FRAG 無しで $`\nu`$ より上の段の $`o_k = \omega`$。
- 2 つの段をまたぐ $`m^*`$ での越え方を、確かめの行つきの独立の段階として書くこと（[SHIFT8-ja.md](SHIFT8-ja.md) §1.2 の細かい点 m5）。
- 最前線より上の $`R_2^S = R_2^C`$：(E)。符号が $`\varepsilon_{G''(\omega+1)+\omega}+1`$ 以上の区域の新しい組での SHIFT のデータと、扇の頂点と蓋での余分な組を除くこと（§1.2）。そして $`\beta_0`$ そのもの
  （予想：$`\beta_0 \ge x_F^C`$。型 F は除かれておらず、$`x_F^C`$ より上では純粋な扇と部分型 (N0) が残る。FAN-LOAD は予想）。$`\kappa_C`$ より上の後続の段階での $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と $`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数：$`\varepsilon_{\Omega_\omega+1}`$ より先の鎖の数 3。$`\Omega_{\omega\cdot 2}`$ より先は、(REP$`^\rho`$)（各単位の中の宿す階数の符号。予想 MARKER-SELF）か段階の道の壁を越える別のやり方、
  そして B-1。そのあと $`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。$`\nu`$ より上の、$`\upsilon`$ の点でない点の名前。
  [COVER-ja.md](COVER-ja.md) §9 の残り。
