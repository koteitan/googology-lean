[← Back](README-ja.md) | [English](SHIFT10.md) | [Japanese](SHIFT10-ja.md)

# $`R_2^+`$ の 38〜40 回目：1 つ上の窓の規則、骨組みの最初の長いやり直し、帰納法としての判定、印のついた源、ちょうどの長い届く先（致命的な点と一部の直し）、単位ごとの容量、Lean での FRAG

このページは [SHIFT9-ja.md](SHIFT9-ja.md) の続き（そこの §3 が 37 回目）。§1 が 38 回目、§2 が 39 回目、§3 が 40 回目。41〜43 回目は [SHIFT11-ja.md](SHIFT11-ja.md)。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。致命的な点か進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことか目標そのものの言い直しにすぎないと言った結果は、進みとして数えない。

**のちに（40 回目、§3）：** §1 と §2 の最前線（$`Z^\varepsilon`$、$`Z^\Lambda`$、$`R_2^S`$ での $`[0, Z^\varepsilon)`$）は $`\nu_C = \nu_S = L(\omega+1)`$ に立つが、それは**書いたままでは証明されていない**（そこへの鎖は、前の値が偽になる符号でのちょうどの長い届く先を使う）。だからこれらも同じ。届く先を使わない部分（符号の側、§1.2 と §2.2 の型、§1.3 と §2.3 の素の符号）は成り立つ。FRAG のもとで、主張は $`R_2^C`$ で $`[0, X_{21}]`$ で証明済み（§3.4）。

**のちに（41 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §1.1）：** 直した値は $`P'`$ より下のどの符号でも証明済み（ENUM-REACH）で、それとともに FRAG のもとで $`\nu_C = \nu_S = L(\omega+1)`$ と $`[0, \nu_C]`$ での主張がもう一度証明された（査読 1 回）。§1 と §2 の $`\nu_C`$ より上の最前線は書いたままでは証明されていないまま：区間の中のちょうどの計算はまだやり直していない。

**のちに（42 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §2.1、§2.2）：** $`Z^\varepsilon`$ と $`Z^\Lambda`$ は $`R_2^C`$ でもう一度証明された（FRAG のもと、定理 C$`^{\Lambda\sharp}`$、やり直しで査読 1 回）。$`\beta_0 \gt Z^\Lambda`$ も。$`R_2^S`$ での $`[0, Z^\varepsilon)`$ は直した値の上では概略で、$`R_2^S`$ での $`[0, Z^\Lambda)`$ は条件つき。$`Z^{\mathrm{LL}}`$ への段階（§1）は証明されていない：その下からの評価は 1 つ下で偽になる着地を写す（予想 FALSE-LB″）。

**のちに（43 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §3）：** 符号全体をやり直しで読んで、段 3 のちょうどの届く先は $`Z^{\mathrm{FP}}`$ より下のどのやり直しでも長い符号も含めて証明され、定理 C$`^{\mathrm{LL}}`$ と C$`^{\mathrm{FP}}`$ は FRAG のもとで $`R_2^C`$ で成り立つ（査読 1 回）。これで §2.1 の B-1 が片づく。FALSE-LB″ は証明済み：§1.1 の LB″ と EXACT-LONG-CL″\*、§2.1 の LB″$`^G`$、強い CROSS″、CROSS-O″、EXACT-LONG″$`^G`$、EXACT-F″ は、直した値が違う所で偽。これらの定理の $`R_2^S`$ の半分は概略。$`R_2^S`$ では主張は $`[0, Z^\Lambda)`$ で成り立つ。$`\nu_3`$（B-2）は含意で仮定に帰着され、その上の半分に新しい進行を止める点がある。

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

ここで $`\delta^\varepsilon`$ はやり直し $`L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega})`$（符号は $`\varepsilon_{G''(\omega+1)+\omega}`$）の点 $`\delta''_1`$ で、$`Z^\varepsilon \lt L(\theta'_2\cdot\omega^2) \lt Z^{\mathrm{LL}}`$。39 回目のあとでは、$`L(\theta'_2\cdot\omega^2)`$ から $`Z^{\mathrm{LL}}`$ までの段階は書いたままでは証明されていない（§2.1）。

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
  そうすれば閉じる (m5)。**のちに（§2.1）：値 $`r(\nu) + o_\nu(m_0)`$ はある $`m_0`$ で偽（2 回目の査読の致命的な点 F-1）。****のちに（43 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §3）：** 直した値は $`Z^{\mathrm{FP}}`$ より下で証明済み。LB″ と EXACT-LONG-CL″\* は $`x_D \ge 2`$ で（FALSE-LB″）、そして $`m_0 \ge \Omega_1`$ で偽。LONG″-$`G''(\omega^2)`$、PIN-ALL″、TOP-REG-FAR″、CROSSED″ は残る。
- **定理 C$`^{\mathrm{LL}}`$ と新しい最前線**（移しで証明済み、FRAG のもと）。$`Z^{\mathrm{LL}}`$ より下ではどのやり直しもちょうどの届く先を持ち、扇の頂点も 3 重の入れ子も無い。だから $`\beta_0 \gt Z^{\mathrm{LL}}`$、
  $`T_3^C \gt Z^{\mathrm{LL}}`$、**$`R_2^C`$ での Wilken の主張は $`[0, Z^{\mathrm{LL}}]`$ で両方の半分とも成り立ち**、**$`[0, Z^{\mathrm{LL}}) \subseteq \mathrm{Core}(R_2^S)`$ で、だから $`R_2^S`$ での主張は $`[0, Z^{\mathrm{LL}})`$ で成り立つ**
  （NO-GAP の議論による、[SHIFT9-ja.md](SHIFT9-ja.md) §3.2）。これは $`R_2^S`$ の最前線 $`Z^\Gamma`$ を越える。1 つの文（「固さの一覧はそのまま成り立つ」）は確かめておらず、要らない：注意 (m6)。
  CODES‴（証明済み）：$`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ より下の骨組みのどのやり直しも、$`\Omega_2`$ より下の符号か $`P_3`$ より下の π の符号を持つ。言い回し (m7)。**のちに（§2.1）：定理 C$`^{\mathrm{LL}}`$ は書いたままでは証明されていない（2 回目の査読の進行を止める点 B-1）。定理 C$`^\Lambda`$ は残る。****のちに（43 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §3）：** $`R_2^C`$ で $`[0, Z^{\mathrm{LL}}]`$ での主張は直した値でもう一度証明された（定理 C$`^{\mathrm{LL}\sharp}`$）。$`R_2^S`$ の部分は概略。
- **未証明**。CROSS″（符号が $`G''(\zeta)`$ 以上、$`\omega^2 \le \zeta \lt b`$ のときの下からの評価 $`r(b) \ge L(\lambda''+\zeta)`$）：概略（§2.1 で証明済み）。未解決：符号が $`G''(\omega^2)^2`$ 以上のちょうどの届く先、$`\omega^2`$ より
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

§3.4 で置き換えた。

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

§3.6 で置き換えた。

## 2. 39 回目

論文は 3 本（2026-10）、どれも査読 1 回：最初の添字の固定点までの骨組みの長いやり直しの論文（§2.1）、(E)：組の種類ごとの補題と扇の論文（§2.2）、素の符号の論文（§2.3）。この節の結果は、
回数を書いていなければ査読 1 回。§1.1、§1.2、§1.3 の査読の細かい点は 3 本の論文が反映し、その査読者がどの直しも確かめた（**査読 2 回**）。**主張の最前線は下がる。** §2.1 の査読者は、
§1.1 の長い届く先のちょうどの値（EXACT-LONG-CL″\*）に致命的な点を、その値を帰納法で使う定理 C$`^{\mathrm{LL}}`$ に進行を止める点を見つけた。どちらにとってもこれが 2 回目の査読。だから FRAG の
もとで、主張は $`R_2^C`$ で $`[0, Z^\Lambda]`$（§1.1 の定理 C$`^\Lambda`$。査読 1 回、$`Z^\varepsilon`$ までは査読 2 回）、$`R_2^S`$ で $`[0, Z^\varepsilon)`$（査読 2 回）で証明済み。ここで

```math
Z^\Lambda = L(\theta'_2\cdot\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2}).
```

査読者は、$`[0, Z^{\mathrm{LL}}]`$ とその先での主張は直したあとも残ると見ている。直しはまだ書かれていない。引く論文：§2.1 は査読済みの段階のほかに Wilken "Σ₁-elementarity and Skolem hull
operators"（APAL 145, 2007。L.2.1、Def 4.1、Thm 2.2、Cor 5.10）、Carlson 2009（Def 5.3、L.5.5、L.5.7）、Wilken の "A glimpse of Σ₃-elementarity"（L.21.10、Thm 21.13）。§2.2 は Carlson 2009（Def 5.3 の
節 2、Def 5.4、L.5.5、L.5.7）、[CW12b]（Prop 7.4 と、型として読んだ Thm 7.9 の証明）、Wilken "Tracking chains revisited" [W17t]、https://arxiv.org/abs/1611.04348（Cor 5.8、たとえとしてだけ）。§2.3 の
証明済みの段階はどの論文も使わず、FRAG も使わない。どの論文も Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない。Lean のファイルは足していない：§2.1 と §2.2 の
順序数の入力は項を比べるだけの Lean のファイルで確かめた（`#eval`、定理は無い。緑で Python と同じ出力。査読者の確かめ直しでも同じ）。§2.3 の査読者は 3 つの段階を別の Lean のファイルで
確かめた（緑）。これらは確かめた扱い。段の番号は [SHIFT8-ja.md](SHIFT8-ja.md) と同じ。「FRAG のもと」もそこと同じ。

記号は §1 と同じ。新しく：$`\hat G'' = G''(\Omega_2) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2})`$ は $`\zeta \mapsto G''(\zeta)`$ の最小の固定点。骨組みのやり直し $`b = L(\lambda'')`$ について
$`F''_b = L(\lambda''+\Omega_1)`$ はその最初の添字の固定点。$`\lambda^{\mathrm{LL}} = \theta'_2\cdot\omega^2+\omega^{G''(\omega^2)^2}`$ で、$`Z^{\mathrm{LL}} = L(\lambda^{\mathrm{LL}})`$。

### 2.1 最初の添字の固定点までの長いやり直し、そして長い届く先のちょうどの値への致命的な点

- **§1.1 の査読の直し**（m1–m7。**査読 2 回**）。届く先についての命題は今はすべて右の上限に沿った 1 つの帰納法で証明する (m5)。§1.2 の致命的な点が挙げたやり直し
  $`L(\theta'_2\cdot(\omega+1)+\varepsilon_{G''(\omega+1)+\omega}\cdot\omega)`$ は $`Z^\Lambda`$ より下にあり、窓の規則により $`\varepsilon_{\delta''_1+\omega}\cdot 2+2`$ に届く。
- **符号の側**（GHAT″、EMPTY″、TIER$`_\zeta`$、OFF″、FIX″、THETA″$`^G`$。証明済み、FRAG 無し。読みは移しで）。$`\hat G''`$ は $`G''`$ の最小の固定点で、$`[\theta'_2\cdot\hat G'', \theta'_2\cdot\Omega_2)`$ の
  添字はどれも $`L`$ の定義域に入らない。段の写像はどの標準形 $`\zeta \lt \hat G''`$ でも働く（$`\zeta \in [\hat G'', \Omega_2)`$ では項 $`G''(\zeta)`$ は標準形でない）。可算の $`x \ge 1`$ について、$`\lambda''+x`$ が定義域に
  入るのは $`x \lt L(\lambda''+x)`$ のときちょうどで、それは $`x \lt F''_b`$ のときちょうど。読みは $`o_b(G''(\zeta)) = L(\lambda''+1+o_b(\zeta))`$ で、$`o_b`$ は $`b`$ での定義域に入る $`\hat G''`$ より下の符号を
  $`[0, F''_b)`$ の上へ写す。可算の $`\zeta`$ ではこれは §1.1 の READ″$`_\zeta`$ で、今は **査読 2 回**。
- **1 つ上の遠い留め**（T$`^F`$、MULTI-RC″$`^F`$、PIN-ALL″$`^F`$、SEP″$`(\Omega_1)`$、TOP-REG-FAR″$`^F`$、LONG-RS″$`^F`$、CROSSED″$`^F`$。移しで証明済み、FRAG のもと）。$`F''_b`$ より下のどの可算の添字の
  距離と、1 つのずれ $`\Omega_1`$ にわたる遠い移し、どの遠い位置での留め。$`\Omega_1+\omega^2`$ までの添字の距離をまたいでも骨組みは保たれる。
- **CROSS″**（移しで証明済み、FRAG のもと。§1.1 では概略）：$`G''(\zeta)`$ 以上の符号は少なくとも $`L(\lambda''+\omega^2\cdot L(\lambda''+1+o_b(\zeta))) \ge L(\lambda''+\zeta)`$ に届く。LB″$`^G`$、R-CAP″$`^G`$、CROSS-O″、
  CROSS-F″（$`\hat G''`$ 以上の符号は $`F''_b`$ に届く）も証明済み。これらは $`m_0 = 0`$ か $`D`$ の読みだけを使う。**のちに（43 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §3）：** この強い CROSS″、LB″$`^G`$、CROSS-O″（$`x \ge 2`$ で）は直した値が低い所で偽で、その判定は取り下げる（証明は小さい符号での前の値を読む）。弱い形 $`r(b) \ge L(\lambda''+1+o_b(\zeta))`$、R-CAP″$`^G`$、CROSS-F″ は残る。
- **致命的な点 F-1：長い届く先のちょうどの値は、ある符号で偽。** 長い符号 $`c = G''(\omega^2)\cdot D + m_0`$ について、§1.1 の値 $`r(L(\lambda'')) = r(\nu) + o_\nu(m_0)`$（EXACT-LONG-CL″\*）と、この論文での
  その広げたもの（$`D \lt \hat G''`$ の EXACT-LONG″$`^G`$、$`D = \hat G''`$ の EXACT-F″、AGREE″ の 1 つの値）は、$`m_0`$ を着地の点 $`\nu`$ で読む。正しくは、定数が $`b`$ より下の符号の上で読まなければ
  ならない。反例：添字 $`\theta'_2\cdot\omega^2+\omega^{G''(\omega^2)+\Omega_1}`$ のやり直し $`b`$（符号は $`G''(\omega^2)+\Omega_1`$、$`Z^{\mathrm{LL}}`$ より下）は $`r(b) = r(\nu) + b`$ で、$`r(\nu) + \nu`$ ではない。
  「$`\le`$」は行き先 $`r(\nu)+b`$ での遠い留めから（$`R_2^+`$ の足し算を使う）、「$`\ge`$」は実現から。符号 $`\hat G''+\Omega_1`$ でも同じことが起きる。当てはまるのは $`\Omega_1`$、$`\Omega_1\cdot k`$、
  $`\omega^{\Omega_1\cdot 2}`$ のような $`m_0`$ で、そこでは定数が $`b`$ より下の小さい符号が共終でない。$`m_0 = 0, 1, P'`$ は当てはまらない。「$`\le`$」の半分は上からの評価として正しいまま。
  **最初の骨組みのちょうどの長い届く先にも同じ欠けがある**：[SHIFT2-ja.md](SHIFT2-ja.md) §3.1 の EXACT-LONG から先（[SHIFT3-ja.md](SHIFT3-ja.md)〜[SHIFT6-ja.md](SHIFT6-ja.md) のその後の形）。前の下からの評価
  RL-UP（[SHIFT-ja.md](SHIFT-ja.md) §9.1）は $`m_0`$ をやり直しの点で読み、直した値と合う。直した式（$`\nu`$ での $`m_0`$ のブロックの、定数が $`b`$ より下の小さい符号の値より上の最小の閉じた点）が
  示されているが、確かめていない。そのような $`m_0`$ でのちょうどの値を、のちのどの結果が使っているかはまだ確かめていない。
- **進行を止める点 B-1：定理 C$`^{\mathrm{LL}}`$ と新しい最前線は、書いたままでは証明されていない。** 定理 C$`^{\mathrm{FP}}`$（$`R_2^C`$ で $`[0, Z^{\mathrm{FP}}]`$、$`R_2^S`$ で $`[0, Z^{\mathrm{FP}})`$ での主張。
  $`Z^{\mathrm{FP}} = L(\theta'_2\cdot\Omega_2+\omega^{\hat G''+G''(\omega^2)}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\hat G''+G''(\omega^2)})`$。途中の最前線 $`L(\theta'_2\cdot\Omega_1)`$ と $`L(\theta'_2\cdot\Omega_2)`$ も）と
  §1.1 の定理 C$`^{\mathrm{LL}}`$ は、F-1 の値で帰納法を進める。直した値はどれも主張した値と同じブロックにあるので、上からの評価、蓋、最前線をまたぐ届く先が無いことは影響を受けず
  （RANGE$`^{\mathrm{FP}}`$：証明済み）、**$`Z^{\mathrm{FP}}`$ より下の CAP-0″**（$`Z^{\mathrm{FP}}`$ より下のどのやり直しも自分をまたがない。上からの評価だけを使う）は証明済み。査読者は、どちらの定理も直したあと
  残ると見ている。**のちに（43 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §3）：** どちらも直した値で $`R_2^C`$ で証明された（定理 C$`^{\mathrm{LL}\sharp}`$ と C$`^{\mathrm{FP}\sharp}`$、査読 1 回）。$`R_2^S`$ の半分は概略。
- **点 $`\nu_3`$**（進行を止める点 B-2）。$`L_3(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + P_3\cdot e)`$、$`\nu_3 = L_3(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + \omega^{P_3+1} + P_3)`$ とする。符号
  $`c_k = G''(\theta'_{k+1}\cdot\omega^2)`$、$`\theta'_k = \psi_{\Omega_{k+1}}(\Omega_\omega\cdot 2)`$ は増えて $`P_3`$ に近づく（証明済み）。論文の判定 SHIFT$`_3`$（$`[0, \nu_3)`$ での 3 つの仮定から $`L_3(\omega) \lt_2^S L_3(\omega+1)`$
  と $`T_3^S = \nu_3`$ が出る）は中身が無い：はじめの仮定（$`\nu_3`$ より下の骨組み）は、ほかの 2 つが与える $`L_3(1) \le_1 L_3(\omega)`$ と両立しない。だから $`\nu_3`$ を 3 つの仮定に帰着させることは
  うまくいかない。うまくいく道は $`\nu_C`$ で使ったもの：1 つ上の CAP-0 と CAP-1、そして NU-CT の類似。細かい点：2 つ目の仮定の区域の上限は符号 1 で偽 (m1)。1 つの添字 (m2)。
  $`m_0`$ が $`\Omega_1`$ のような場合の例 (m3)。$`R_2^S`$ の側は B-1 に頼る (m4)。**のちに（43 回目、[SHIFT11-ja.md](SHIFT11-ja.md) §3）：** CAP-0″、CAP-1″、NU-CT を通る道は含意として書かれた。上の半分 $`T_3^S \le \nu_3`$ は証明されていない（新しい進行を止める点）。
- **未証明。** EXACT-LONG″（F-1）。定理 C$`^{\mathrm{LL}}`$、C$`^{\mathrm{FP}}`$ と途中の最前線（B-1）。SHIFT$`_3`$ と $`\nu_3`$ の帰着（B-2）。未解決：$`\hat G''+G''(\omega^2)`$ からの符号（$`F''_b`$ での着地の
  あとの族）、$`\zeta \ge \Omega_2`$ の段 $`G''(\zeta)`$、深さ 2 以上の着地の計算、$`P_3`$ より下の CAP-0 と 1 つ上の NOT-LOW（概略）、1 つ上の包の蓋 READ$`^\sharp`$（予想）。

### 2.2 (E)：組の種類ごとの補題、最小の扇

言葉は §1.2 のもの。

- **§1.2 の査読の直し**（F-1 と m1–m7。**査読 2 回**）。場所の主張は取り下げ、査読者の命題に置き換えた：$`\upsilon`$ の点 $`d`$ の切片の $`d`$ 以外のどの点も共終な Pred₁ を持たない
  （NOBAD と INC1、[BREAK-ja.md](BREAK-ja.md) §1）。SEG-GAP⁺（証明済み）：最初のブロックが分かっている計算の基の点で、$`\delta''_1`$ と、その次の極限の添字の $`\upsilon`$ の点との間のどの点も
  共終な Pred₁ を持たず、$`\beta_0`$ と $`T_3^C`$ はその点以上（§1.2 の査読者の注意 m1。今は証明済み）。
- **組の種類ごとの補題**（K01、K2。証明済み。K01 は FRAG 無しでどの $`\upsilon`$ の点でも、K2 は移しで FRAG のもと）。共終な Pred₁ を持つ左端 $`t`$ について、Carlson 2009, Def 5.3 の節 2 だけを使う
  補題が、$`\beta_0`$ より下の $`R_2^C`$ での $`t`$ の後の点は $`R_2^S`$ での後の点の中にあることを示す：届く先が次の $`\upsilon`$ の点である $`\upsilon`$ の点 $`t`$（種類 K01）と、§1.1 の骨組みを持つ区域の
  $`\tau''_j`$（種類 K2）。組の証明（PAIR、相対化した PAIR、SHIFT）とあわせ、どの種類も判定を満たす。査読者：K01 は記述 SKEL$`^\infty`$（[COVER-ja.md](COVER-ja.md) §5.1）の $`\tau`$ の点として定める
  べき (m3)。
- **CRIT-IND$`^K`$**（証明済み）。$`b`$ より下で共終な Pred₁ を持つどの $`\alpha`$ も種類 K01 か K2 で、$`b`$ より下で $`R_2^S`$ に 3 重の入れ子が無ければ、$`\beta_0 \ge b`$、$`T_3^C \ge b`$ で、右端が $`b`$ より
  下のどの組も判定を満たし、そこで一様な有限集合の試験も必要。だから CRIT-IND（§1.2）の仮定はそこで、仮定するのでなく証明される。
- **CAP-PERSIST、SKEL″$`^x`$、UPPER″、PRED1″、UNIFORM-A**（証明済み。移しで、FRAG のもと）。区域の組の骨組みに要るのは、その下の骨組み、届く先の上からの評価、共終な Pred₁ を
  持つやり直しが無いことだけ。ちょうどの届く先は要らない。UNIFORM-A は型：$`Z'`$ より下のどのやり直しも、届く先が計算で与えられるか $`Z'`$ に届き、どれも共終な Pred₁ を持たなければ、
  $`\beta_0 \ge Z'`$、$`T_3^C \ge Z'`$、$`Z'`$ より下で一様な試験は必要で、主張は $`R_2^C`$ で $`[0, Z')`$ で成り立つ。査読者：計算された届く先を持つまたぐ点が着地する区域には §1.1 の CROSSED″ が
  要る (m4)。言い回し (m6)。
- **定理 C$`^{\mathrm{LL}}`$ に頼る結果**（その査読者は FRAG のもとで証明済みと認めたが、§2.1 が B-1 を見つけた定理 C$`^{\mathrm{LL}}`$ を使うので、B-1 が直るまで **数えない**）：LOAD$`^{\mathrm{LL}}`$
  （右端が $`Z^{\mathrm{LL}}`$ 以下のどの組も種類 K01 か K2 で、判定を満たす）。C$`^{\mathrm{LL}\sharp}`$（$`\beta_0 \gt Z^{\mathrm{LL}\sharp}`$ と、$`R_2^C`$ での $`[0, Z^{\mathrm{LL}\sharp}]`$ での主張）。C$`^{\mathrm{LX}}`$
  （$`\beta_0 \gt Z^{\mathrm{LX}}`$ と、$`R_2^C`$ での $`[0, Z^{\mathrm{LX}}]`$ での主張。査読者：書き方が循環しているが、右の上限に沿った 1 つの帰納法で直せる、m1。端の点でのちょうどの届く先は
  証明されていない、m2）。ここで

```math
Z^{\mathrm{LL}\sharp} = L(\lambda^{\mathrm{LL}}+\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{\omega^{G''(\omega^2)\cdot 2}} + \omega^{P'+2}),\qquad Z^{\mathrm{LX}} = L(\lambda^{\mathrm{LL}}+\omega^2\cdot Z^{\mathrm{LL}\sharp}).
```

  条件つき（概略）：符号 $`G''(\omega^2)^2`$ のやり直しの届く先がどこに着地するかについての未解決の命題のもとで、$`\beta_0 \ge L(\theta'_2\cdot\omega^2+\omega^{G''(\omega^2)^2+1})`$。
- **扇**（FAN-SHAPES、LEAST-FAN。証明済み）。部分型 (N0) が起きるのは、左端での $`R_2^C`$ の扇が開いている（下の後の点が $`\beta_0`$ に $`\le_1`$ でない）ときちょうど。型 F には閉じた扇が要るので、
  その左端は閉じた扇の最小の頂点 $`f_0^C`$ 以上で、それは $`x_F^C`$ より上。最小の扇 $`x_F^C`$ では、最初の食い違いは 2 つだけ：$`\beta_0 = y_1`$（型 N）か、$`\beta_0 = y_2`$ の (N0)。そこで型 F は起きず、
  そこでの (N0) は $`R_2^S`$ の最小の扇の上端を $`R_2^C`$ のものより上に置く。CI-EXTRA：余分な組では、ずらし、載せ、上限のどのデータも無い（はじめの文は証明済み。「だから…」の文は未証明、m5）。
- **LOAD-SHAPE への進行を止める点 B-1。** 最小の扇の載せは自分の頂点を使えない、という主張は証明されていない：頂点自身の区間の中に長い組がある（$`\Pi_2`$ の文が下から上がる）ので、
  [CW12b] Thm 7.9 の証明のように、載せがそれを通るかもしれない。だから FAN-LOAD への道の一覧は欠けている。(E) については失うものは無い：NO-SELF-LOAD（§1.2）は分ける集合ではなお
  成り立つ。FAN-LOAD：予想。CRIT-IND が最初に破れうる場所の論文の一覧は注意：それで全部であることは証明されていない (m7)。
- **未解決。** (E)。FAN-LOAD。$`\beta_0 \ge x_F^C`$（予想）。

### 2.3 素の符号：単位ごとの容量、$`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ を越える最初の評価

- **§1.3 の査読の直し**（m1–m8。査読者が確かめた）。REP-RANK はその部分 (i)–(iii) だけを残す。「(REP$`^\rho`$) が成り立つのは $`\rho(H)`$ が $`H`$ の中に符号を持つときちょうど」と「壁は
  (REP$`^\rho`$) が成り立たないことと同値」は取り下げ (m1)。PER-KIND は窓の降下を使う (m2)。NO-FIX は 2 つの仮定を持つ (m3)。
- **LEX-CAP、MARK$`^{\mathrm{lex}}`$、UNIT-SUP$`^{\mathrm{lex}}`$**（証明済み）。単位 $`U`$ ごとの容量を辞書式の順で比べる：（添字、種類、$`\alpha(U)`$、$`n(U)`$ から深さを引いたもの）。$`n(U)`$ が $`U`$ の源の
  深さ以上で、1 つの添字の類の中で $`(\alpha, n)`$ が減らなければ、どの 2 つの単位でも (C1)–(C3) を満たす。深さの項が真の段差を与える。そのような容量は印で実現されるので、§1.3 の宿す補題が
  使える。PER-KIND とは矛盾しない：容量は値と深さだけでなく単位で決まる。
- **ALPHA-LOW、REDUCTION**（証明済み）：すぐ下で源の深さが限りなく大きくなるどの単位でも、$`\alpha`$ は跳ばなければならない。**RHO-LEAF**（書いたままで証明済み）：$`\Omega_{\omega\cdot 2}`$ より下の
  $`\psi_{\Omega_{\omega+1}}(\Omega_{\omega+5} + \omega^{\Omega_{\omega+3}+b})`$ の宿す階数 $`\rho`$ は、どの $`b \lt \Gamma_0`$ でも $`b`$ 以上。査読者：単位はもう $`b`$ の符号を持っているので、これは単位ごとに 1 つの印が
  求めすぎだとは示さない (m1)。MARKER-SELF は脇に置く。反証ではない。
- **例**（LEVEL-BOUND、LEX$`[\Omega_{\omega\cdot 2}]`$、UNITS、SC-MAX、LEX$`[S_*]`$。証明済み）。$`\Omega_{\omega\cdot 2}`$ までの段階の集合では $`\alpha = 0`$ で足り、$`S_*`$（下）までは有限の桁で $`\alpha \lt \omega^{\omega+1}`$
  で足りる。ALPHA-LOW$`^\Gamma`$（証明済み）：さらに上には、そのようなどの容量でも $`\alpha \ge \Gamma_0`$ となる単位がある。「有限の桁は $`S_*`$ で止まる」は未証明（注意、m2）。
- **新しい素の評価**（$`S_*`$ までの段階の集合での REGION、SHAPE、IDX。移しで証明済み）：

```math
\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*),\qquad S_* = e_* + \psi_{\Omega_{\omega+1}}(e_*),\quad e_* = \Omega_{\omega\cdot 2} + \psi_{\Omega_{\omega+2}}(\Omega_{\omega\cdot 2})\cdot\omega^\omega,
```

  そして $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2}) \lt \psi_{\Omega_1}(S_*) \lt \psi_{\Omega_1}(\Omega_{\omega\cdot 2}\cdot 2)`$。だから $`\psi_{\Omega_1}(S_*)`$ より下で鎖の数 5 で RED-TOWER が成り立ち、$`m_F \gt \psi_{\Omega_1}(S_*)`$。これは
  $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ を越える最初の素の評価：「鎖の数を固めると段階の道は $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ で止まる」は鎖の数 5 で偽で、§1.3 の壁はそこで挙げた容量の形でだけ
  成り立つ。$`\psi_{\Omega_1}(S_*)`$ が $`\iota(\mathrm{CH}_4)`$ より上かどうかは分かっていない (m7)。細かい点：UNITS の 1 つの理由 (m3)、1 つの上限 (m4)、見出しの 1 つの条件 (m5)、1 つの節の範囲 (m6)
  と確かめの範囲 (m8)。
- **未解決。** LEX-SELF（$`\alpha`$ を各単位自身の境の符号から読む）：予想。それがあれば（概略）$`\psi_{\Omega_1}(\Omega_{\omega\cdot 2+1})`$、$`\theta_0`$、$`H_m`$、「最初の扇は到達不能基数を要する」。配置 B（B-1）。
  鎖の数 4 が $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$ を越えるか。

### 2.4 39 回目のあとの状態

§3.4 で置き換えた。

### 2.5 39 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §2.1。9 回の実行（固定点、$`\hat G''`$ より下の段、ずれの定義域、読み、遠い移し、名前の鎖、符号 $`c_k`$）、食い違い 0。試験の道具の誤りを 4 つ見つけて直し、論文はそのことを書いている。
  Lean は緑で Python と同じ。査読者：4 つの基で 100 個の一般の可算のずれ、食い違い 0。定義域の 337 個の添字で符号の上限の破れ 0。F-1 と m1 の反例、B-2 の点。著者の Lean のファイルの
  再実行は同じ出力。
- §2.2。4 回の実行（$`Z^{\mathrm{LL}}`$ の区域の符号と点、届く先の分からないやり直し、最小の扇の形）、失敗 0。Lean は緑で Python と同じ。査読者：実行の再実行は同じ出力。600 個のでたらめな
  添字のうち、$`Z^{\mathrm{LL}}`$ と $`Z^{\mathrm{LX}}`$ の間の 147 個はすべて予想どおりの形。Lean のファイルの再実行は緑。$`R_2^S`$、$`R_2^C`$、届く先、写し、判定は計算できない。
- §2.3。LEX-CAP の 2 つの条件を、種ごとに 380 個のでたらめな引数、2 つの種で（約 71,700 の順序のついた組、深さ 6 まで）。$`S_*`$、RHO-LEAF、証拠の族、ALPHA-LOW$`^\Gamma`$ も。失敗 0。
  査読者：どちらの種の再実行も同じ出力。自前の深さの読み手で 2 つの種（種ごとに約 51,000 組、より深い入れ子、より多くの類）、失敗 0。(C1) の真の段差、ALPHA-LOW、REDUCTION の Lean の
  ファイル、緑。確かめは引数の 1 つの類だけを覆う (m8)。

### 2.6 未解決

§3.6 で置き換えた。

## 3. 40 回目

論文は 3 本（2026-10）：長い届く先のちょうどの値を直す論文（§3.1）と、記録した結果のどれが偽の値を使うかの確かめ（§3.2）は、どちらも査読 1 回。$`R_2^C`$ の Lean の最初の段階（§3.3）は、
公理と定義を確かめる監査を受けた（証明は Lean が確かめる）。この節の結果は、回数を書いていなければ査読 1 回。§2.1、§2.2、§2.3 の査読の細かい点は §2 の記録にもう入っている。

**主張の最前線は下がり、節目はもう証明済みではない。** どちらの査読者も、$`\nu_C = \nu_S = L(\omega+1)`$ への鎖（[SHIFT7-ja.md](SHIFT7-ja.md) §2.1）と $`X_{21}`$ より上のどの最前線も、前の値が偽になる
符号でのちょうどの長い届く先を使うことを見つけた。だから **$`\nu_C = \nu_S = L(\omega+1)`$、$`[0, \nu_C]`$ での Wilken の主張、not-LOW、そして $`X_{21}`$ より上のどの範囲（$`Z^\Lambda`$ まで）も、書いた
ままでは証明されていない。** FRAG のもとで、主張は $`R_2^C`$ で $`[0, X_{21}]`$ で証明済み（直した証明、査読 1 回。§3.2 の点 $`X_{19}^{\mathrm{lin}}`$ までは 2 つの証明で査読 2 回）。$`R_2^S`$ では
FRAG 無しと同じく $`\upsilon_{\omega^3}`$ までだけ。ここで

```math
X_{21} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_H + \omega^{G(\hat\zeta_H)+1}\cdot 2),\quad \hat\zeta_H = \theta_3\cdot\Omega_3 + \omega^{\hat g_3+g_3},\quad \theta_3 = \psi_{\Omega_4}(\Omega_\omega),
```

$`\hat g_3 = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot\Omega_3)`$、$`g_3 = \psi_{\Omega_3}(\Omega_\omega + \theta_3\cdot\omega^2)`$（[SHIFT5-ja.md](SHIFT5-ja.md) §2.1）。FRAG そのものは今は 2 本の論文から引いた 20 個の事実から
Lean で証明済み（§3.3、[LEAN-ja.md](LEAN-ja.md)）。

引く論文：§3.1 と §3.2 は査読済みの段階のほかに Wilken "Σ₁-elementarity and Skolem hull operators" [W07b]（APAL 145, 2007。L.2.1）、Wilken "Ordinal arithmetic based on Skolem hulling" [W07a]
（APAL 145, 2007）、Wilken の "A glimpse of Σ₃-elementarity"（Prop 21.6）、Carlson 2009。§3.3 は Carlson 2009（Def 2.1、2.3、2.6、5.2–5.4、定義のためだけ）と [W07a]、[W07b]（引いた事実。
[LEAN-ja.md](LEAN-ja.md) に一覧）。どれも Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない。[W07b] の L.2.1 と Thm 2.2 の主張は [W07b] §2 から取る。段の番号は
[SHIFT8-ja.md](SHIFT8-ja.md) と同じ。

記号：やり直し $`\lambda`$ について、$`R_1 = \rho_{\lambda+\omega^2}`$ は次のやり直し、$`\delta_R`$ はやり直し $`R`$ の最初のブロックの上端（[REACHES-ja.md](REACHES-ja.md)）、$`\Theta_\lambda = o_\lambda`$ は $`\lambda`$ での
符号の読み（定数が $`\rho_\lambda`$ より下の、より小さい符号の順序型）、$`\hat G = G(\Omega_2)`$、$`F_\lambda = H(\eta_\lambda + \Omega_1)`$ は $`\lambda`$ より上の最初の添字の固定点。長い符号は
$`m = G_2\cdot D + m_0`$、$`D \ge 1`$、$`m_0 \lt G_2`$。

### 3.1 $`\hat G + G_2`$ より下で直した長い届く先のちょうどの値、そして最前線 $`X_{21}`$

- **誤りは F-1 より広い**（査読者が自分で診断を確かめた）。やり直し $`\lambda`$ の実現は $`\rho_\lambda`$ より下にあるので、その符号の定数は $`\rho_\lambda`$ より下だけ。長い届く先の下からの評価の前の
  証明（[SHIFT2-ja.md](SHIFT2-ja.md) §3.1 の EXACT-LONG と CROSS-O から先）は、定数が着地の点 $`\rho_\nu`$ までの符号を実現の符号として使っていた。これは $`m_0`$ の部分（§2.1 の F-1）も、$`D`$ の
  部分によるまたぎも壊す。符号は全体を $`\lambda`$ で $`\Theta_\lambda`$ により読まなければならず、着地のやり直しは $`\Theta_\lambda(m)`$ 以下で最大のやり直しの点で、$`\upsilon_{\lambda+\omega^2\cdot\Theta(D)}`$ ではない。
- **反例**（移しで証明済み、FRAG のもと。$`X_6`$ より下のやり直しで、そこではどの仮定も成り立つ。証拠は確かめた）。$`x \lt G_2`$ の符号 $`G_2 + x`$ では $`r(\lambda) = \delta_{R_1} + 1 + \Theta_\lambda(x)`$。
  だから $`G_2 + \Omega_1`$ は $`\delta_{R_1} + \rho_\lambda`$ に届く。$`G_2 + \Omega_1 + 1`$ は $`\delta_{R_1} + \rho_\lambda + 1`$ に届くので、§2.1 で示された直しは偽。$`G_2 + \varepsilon_{\Omega_1+1}`$ は
  $`\delta_{R_1} + \varepsilon_{\rho_\lambda+1}`$ に届くので、§2.1 が影響を受けないとした符号の一覧は誤り。**NO-CROSS**：符号 $`G_2\cdot 2`$ は $`\delta_{R_1} + R_1 \lt \rho_{\lambda+\omega^2\cdot 2}`$ に届くので、
  CROSS-O は $`x = 2`$ で偽で、前の着地は $`2 \le D \lt \hat G`$ のどれでも誤り。証拠はやり直し $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2\cdot 2})`$。17 回目の査読済みの評価（RL-UP と
  $`G_2\cdot 2`$ より下の符号の蓋、[SHIFT-ja.md](SHIFT-ja.md) §9.1）はこれらの値と合う。
- **定理 TRANSLATION**（移しで証明済み、FRAG のもと）。$`K_\lambda`$ を、どの $`\alpha \in (\rho_\lambda, y]`$ も $`\mathrm{lh}(\alpha) \le y`$ となる点 $`y \ge \delta_\lambda`$ の集まり（$`\lambda`$ の届く先になりうる点）、
  $`k_\lambda`$ をその増える数え上げとする。$`\nu_S`$ と $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ より下の長いやり直し $`\lambda`$ で、符号（または π 符号）$`m`$ が $`G_2 \le m \lt \hat G + G_2`$ のものすべてで：

```math
r(\lambda) = k_\lambda(\Theta_\lambda(m)) = F(\nu, \tau_\nu + x),\qquad \rho_\nu = \Theta_\lambda(m) \text{ 以下で最大のやり直しの点},\quad x = \Theta_\nu^{-1}(-\rho_\nu + \Theta_\lambda(m)).
```

  $`F`$ は $`\nu`$ での短い符号の値（[SHIFT6-ja.md](SHIFT6-ja.md) §3.1）。「$`\ge`$」は定数が $`\rho_\lambda`$ より下の実現から、「$`\le`$」は $`R_2^+`$ の足し算と行き先のどの成分の留めも使う遠い留めから。
  MONO♯（値は符号とともに増える）、TF5♯（どの遠い移しとも、動く定数があっても入れかわる）、BC♯（基の取りかえ）も。区域 $`[m^*, \psi_{\Omega_1}(\Omega_\omega\cdot 3))`$ でも同じ。査読者の細かい点：
  符号の定義域は査読済みの包でなければならず、上限 $`\kappa_0`$ の選び方で π 符号の尾が消える (m1)。1 つの移しは相対的なもの (m2)。BC♯ には有限の閉じ方の判定が要る（m3。以下では使わない）。
  「新しい値は前の値以下」は査読されていない監査から取っていたので、査読者が直接の証明を与えた (m4)。
- **SHARP-CROSS**（証明済み）。$`F_\lambda`$ より下で：$`\rho_\lambda`$ より下の $`\omega^2`$ の可算の倍数 $`\zeta \ge \omega^2`$ のどれでも、$`r(\lambda) \ge \upsilon_{\lambda+\zeta}`$ は $`m_\lambda \ge G(\zeta)`$ のときちょうど。
  これは 17 回目の予想だった。
- **FAR-PIN$`^{L\sharp}`$**（移しで証明済み、FRAG のもと）：[SHIFT5-ja.md](SHIFT5-ja.md) §1.1 の遠い留めを、ちょうどの原子を直した値にして、$`\hat G + G_2`$ より下のどの長い前置きの符号でも。
  だから着地の蓋 LAND-CAP、LAND-CAP$`^G`$、LAND-CAP$`^F`$、CAP$`^\sharp`$、$`\hat\zeta_H`$ より下の READ$`^\sharp`$（[SHIFT5-ja.md](SHIFT5-ja.md) §1.1、§2.1）は成り立ち、それとともに $`X_{19}`$、$`X_{20}`$、$`X_{21}`$ も。
- **定理 X21 をもう一度**（移しで証明済み、FRAG のもと）：$`\nu_C \ge X_{21}`$、$`\nu_S \ge X_{21}`$、そして **$`R_2^C`$ で $`[0, X_{21}]`$ での Wilken の主張、両方の半分**。証明が長い前置きの原子に
  出会うのは $`\hat G + G_2`$ より下の符号だけ（この上限は前と同じく 889 個の乗数で確かめた）で、$`D`$ の部分からの下からの評価は使わない。直した形は査読 1 回 (m6)。
- **未証明。** $`X_{21}`$ より上：$`X_{22}`$、$`X_{23}`$（[SHIFT6-ja.md](SHIFT6-ja.md)）、$`P'`$ より下の CAP-0、CAP-1、$`\nu_C \ge L(\omega+1)`$（[SHIFT7-ja.md](SHIFT7-ja.md) §1.1）とそれより後の段階すべて。
  これらは $`\hat G + G_2`$ 以上の符号での原子かまたぎを使う。$`P'`$ より下のどの符号での値も予想 ENUM-REACH：$`\hat G + G_2`$ より先では届く先が長いやり直しをまたぐので、着地の計算を新しい
  着地でやり直さなければならない（のちに：証明済み、[SHIFT11-ja.md](SHIFT11-ja.md) §1.1。届く先が最初に長いやり直しをまたぐのは符号 $`G(\hat\zeta_3)`$ で、$`\hat G + G_2`$ のすぐ先ではない）。**1 つ上**（概略で数えない。査読の進行を止める点 B-1）：$`\hat G'' + G''(\omega^2)`$ より下の TRANSLATION″ と定理 C$`^{\mathrm{LL}\sharp}`$、C$`^{\mathrm{FP}\sharp}`$
  （$`R_2^C`$ で $`[0, Z^{\mathrm{FP}}]`$ での主張）。どれも (H0) = $`P'`$ より下の ENUM-REACH と、それの上で $`\nu_C`$ への鎖をもう一度証明したもの、のもと。TRANSLATION″ の証明は道具を並べるだけ。
  概略では符号 $`G''(\omega^2)\cdot 2`$ は $`L(\lambda''+\omega^2\cdot 2)`$ に届かないので、§2.1 の CROSS″ の最初の不等式は取り下げる。弱い形 $`r \ge L(\lambda''+\zeta)`$ は概略の一部として残す。

### 3.2 確かめ：どの結果が偽の値を使うか

- **いちばん簡単な場合の直した値**（証明済み、FRAG のもと）。UB：前の証明の「$`\le`$」の半分はそれだけで成り立つ。BRACKET：2 つの読みは $`m_0 \ge \Omega_1`$ のどこでも違う。**CV-LIN**：
  $`D = 1`$、$`c \lt \rho_\lambda`$ の $`m_0 = \Omega_1\cdot k + c`$ で $`r(\lambda) = r(\nu) + \rho_\lambda\cdot k + c`$（査読者が $`m_0 = \Omega_1`$ での段階を手でやり直した。RL-UP とも §3.1 とも合う）。FALSE-ω：
  $`m_0 = \Omega_1\cdot\omega`$ では届く先は $`r(\nu) + \rho_\nu`$ 以下で、前の値より下。PIN-LIN：これらの符号では直した原子で遠い留めが働く。LB-CORR（前の着地 $`\nu`$ での
  $`r(\lambda) \ge r(\nu) + \Theta_\lambda(m_0)`$）：その査読者は小さい $`m_0`$ では証明済み、その上では未証明とした（進行を止める点 B-1：その段階には直した値の移しでの不変性が要り、それは未解決）。
  §3.1 の NO-CROSS により、その前の着地は $`2 \le D \lt \hat G`$ で誤りなので、数えるのは $`D = 1`$ だけ。
- **影響を受ける符号が最初に出る所**（証明済み、確かめた）。$`\zeta_1 = \hat\zeta_3 + \omega^{g_3+\Omega_2}`$（$`\hat\zeta_3 = \theta_3\cdot\omega^2`$）とすると、$`G(\zeta_1)`$ より下ではどの着地の前置きも $`m_0 \ge \Omega_1`$ を
  持たず、$`\zeta_1`$ が $`m_0 = \Omega_1`$ の最初の前置きを与える。これは $`X_{19}`$ の着地の蓋の範囲の中。査読者：可算の残りは有限だけでなく $`\omega`$、$`\varepsilon_0`$、$`\varphi(2,1)`$ もありうる (m4)。結論は
  変わらず、その探索は 2,512 個の正規の乗数で反例 0。
- **$`X_{19}^{\mathrm{lin}}`$**（証明済み、FRAG のもと）。$`\zeta_{\mathrm{lin}} = \hat\zeta_3 + \omega^{g_3+\Omega_2\cdot\omega}`$ として、$`\nu_C \ge X_{19}^{\mathrm{lin}} = \psi_{\Omega_1}(\Omega_\omega + \zeta_{\mathrm{lin}} + \omega^{G(\zeta_{\mathrm{lin}})+1}\cdot 2)`$、
  $`\nu_S \ge X_{19}^{\mathrm{lin}}`$ で、主張は $`R_2^C`$ で $`[0, X_{19}^{\mathrm{lin}}]`$ で成り立つ。$`\zeta_{\mathrm{lin}}`$ の代わりに $`\zeta_1`$ とした $`X_{19}^\flat`$ は新しい補題無しで成り立ち、
  $`X_{18} \lt X_{19}^\flat \lt X_{19}^{\mathrm{lin}} \lt X_{19} \lt X_{21}`$。$`D = 1`$ の符号だけを使うので、B-1 にも §3.1 にも触れない。§3.1 とあわせて $`X_{19}^{\mathrm{lin}}`$ より下の主張の 2 つ目の証明：**査読 2 回**。
- **節目は書いたままでは証明されていない**（査読者が確かめた）。CROSS-LIM（[SHIFT7-ja.md](SHIFT7-ja.md) §2.1）は符号 $`G_2 + P`$ のやり直しをまたぐが、その届く先は挟まれているだけで、長い
  やり直しの段階にはそのちょうどの値と移しでの不変性が要る。だから CROSS-LIM、ずらしの判定の仮定 (C1)–(C3)、PAIR、UP、NU、NU-NAME、LOW$`^\infty`$ は書いたままでは証明されていない。
  $`[G_2, P')`$ のどの符号でも蓋を要る not-LOW、$`P'`$ より下の CAP-0、CAP-1 も同じ。成り立つもの：判定 SHIFT そのもの、核の半分 $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$、LC-STRICT の符号の不等式、
  移しの補題。確かめは、直した値で節目が戻ると見ている（予想）。「もっと短い道は無い」は注意で、証明ではない (m5)。
- **表**（[AUDIT-ja.md](AUDIT-ja.md)）。$`X_9`$ から $`X_{18}`$ は成り立つ（影響を受ける符号でのちょうどの長い値を使わない）。$`m_0 \ge \Omega_1`$ でのちょうどの長い式（[SHIFT2-ja.md](SHIFT2-ja.md) §3.1 の
  EXACT-LONG、[SHIFT3-ja.md](SHIFT3-ja.md)〜[SHIFT6-ja.md](SHIFT6-ja.md) のその形、[SHIFT4-ja.md](SHIFT4-ja.md) §2.1 の EXACT-LONG-CL\*、[SHIFT7-ja.md](SHIFT7-ja.md) §1.1 の LAND$`^\omega`$）は書いたとおりでは偽で、
  上からの評価は成り立つ。$`X_{21}`$ より上に記録したものはどれも書いたままでは証明されていない：$`X_{22}`$、$`X_{23}`$、$`L(\omega+1)`$、$`\nu_C = \nu_S`$、$`X_A`$、$`L(\omega^2)`$、$`L(\Omega_1\cdot\omega)`$、
  $`L(\varepsilon_{\Phi_\Omega+1})`$、$`L(G_2)`$、$`L(\Omega_2+\Phi^{P'}\cdot\omega)`$、$`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)`$、$`Z^\Gamma`$、$`Z^\varepsilon`$、$`Z^\Lambda`$、そして $`R_2^S`$ での範囲 $`[0, Z^\varepsilon)`$。確かめは
  $`X_{19}`$ から $`X_{21}`$ も未証明としたが、§3.1 がそれを直す。
- **一覧への査読の進行を止める点**（B-2、B-3）。[SHIFT2-ja.md](SHIFT2-ja.md) §3.1 の下からの評価の段階 (b) は、制限しても同じ欠けがあり、そこの挟み込みの下の端も同じ。影響を受ける符号での
  ちょうどの長い式はほかにも [SHIFT3-ja.md](SHIFT3-ja.md) §1.1、§2.1（EXACT-LONG の形）、[SHIFT4-ja.md](SHIFT4-ja.md) §1.1（EXACT-LONG-CL）、[SHIFT5-ja.md](SHIFT5-ja.md) §2.2（段 2 の形）、
  [SHIFT6-ja.md](SHIFT6-ja.md) §1.2（EXACT-LONG$`^e`$）にあり、これらも書いたとおりでは偽。$`X_{15}`$ までの範囲は影響を受けない。もう一度証明した $`X_{21}`$ より下にあるから。（のちに [SHIFT11-ja.md](SHIFT11-ja.md) §1.2 の監査が B-2 と B-3 を片づけた：段階 (b) は制限しても偽（LB-b-FALSE）、$`X_9`$ から $`X_{18}`$ は書いたままで成り立ち、$`X_{19}`$ から $`X_{21}`$ は FAR-PIN$`^{L\sharp}`$ で成り立つ。）
- **数えないもの。** 表の「直した値で成り立つ」という判定（未解決の予想 CV とその不変性と留めに立つ）と、もう一度証明すべきものの一覧。その一覧は §3.6 の計画。

### 3.3 Lean、段階 1：$`R_2^C`$、核、FRAG

- **$`R_2^C`$ は Lean で定義し、仮定しない。** $`\le_1`$ と $`\le_2`$ は Carlson 2009, Def 5.3–5.4 のとおりに、右端についての再帰で定める（Def 2.1、2.3、5.2 も）。$`R_2^C`$ に触れる公理は無いので、
  論文の読み違いは Lean の $`R_2^C`$ を Carlson のものと違うものにしうるだけで、公理どうしを矛盾させることはできない。Lean の標準の 3 つのほかに公理を使わずに、Lean は次を証明する：再帰の等式。
  $`\le_1`$ と $`\le_2`$ は反射的、推移的で $`\le`$ の中。区間と極限の性質。Carlson 2009, L.5.5 (1)、(3)–(6)。$`x`$ がそれより大きいどの順序数とも $`\le_1`$ でない限り届く先 $`\mathrm{lh}(x)`$ がある。
  どの解釈でも同型最小の集合と核（Def 2.6）。補題 LOC とその系。
- **Lean での定理 FRAG**、可算の基がいくつでも（定義域は論文の証明のものを含むので、Lean の命題のほうが強い）。補題 ST、定義域全体での基 1 つの FRAG、Lean の $`R_2^C`$ についての
  定理 FRAG2（$`R_1^+`$ の $`\le_1`$ の定数だけを使う）も。これらは 1 つのファイルの 27 個の公理を使う：7 個の定数（$`R_1^+`$ の $`\le_1`$、Wilken の項の体系 $`T^\tau`$、そのパラメタ、基の取りかえ
  $`\pi_{\sigma,\tau}`$、高さ、2 つの項の族）と、[W07a] と [W07b] から引いた 20 個の事実。
- **監査**：どの公理も論文に忠実（8 個は引いた 2–3 個の節を 1 つにしたもので、どのつなぎも確かめた）、どの定義も正しく、どの主な定理も Lean で証明済み。致命的な点も進行を止める点も無い。
  細かい点：$`R_1^+`$ についての 3 つの事実は手元に無い論文で証明され、主張は [W07b] §2 にある (m1)。FRAG は可算の基を要る (m4)。モジュールは 1 つにまとめた形でだけ作られた（m5。リポジトリ
  では今はモジュールとして作られる）。説明の文にローカルのファイル名があった（m6。置き換えた）。Lean の $`\upsilon`$ が Wilken の $`\upsilon`$ であることはまだ示していない (m7)。$`R_1^+`$ の $`\le_1`$ と
  $`R_2^C`$ の $`\le_1`$ のつながりはまだ無い (m9)。
- だから「FRAG のもと」は今は「2 本の論文から引いた 20 個の事実のもと」の意味で、FRAG の論文での証明はもう査読を要らない。ファイル、出典つきの公理、定理は [LEAN-ja.md](LEAN-ja.md) にある。

### 3.4 40 回目のあとの状態

- **$`R_2^C`$ での Wilken の主張**：FRAG 無しで $`[0, X_4]`$、そして **FRAG のもとで $`[0, X_{21}]`$** で両方の半分とも成り立つ（$`[0, X_{18}]`$ は前と同じく査読 2 回。$`X_{19}^{\mathrm{lin}}`$ までは
  2 つの証明で査読 2 回、§3.1、§3.2。$`X_{19}^{\mathrm{lin}}`$ から $`X_{21}`$ までは直した証明の査読 1 回）。核の半分は $`[0, \nu_C]`$ で成り立ち、FRAG のもとで $`\nu_C \ge X_{21}`$。**書いたままでは
  証明されていない**：$`\nu_C = \nu_S = L(\omega+1)`$、$`[0, \nu_C]`$ での主張、そして [SHIFT6-ja.md](SHIFT6-ja.md)〜[SHIFT9-ja.md](SHIFT9-ja.md) とここの §1、§2 に記録した $`X_{21}`$ より上のどの範囲も。
- **$`R_2^S`$ での Wilken の主張**：証明済みなのは $`\upsilon_{\omega^3}`$ までだけ（FRAG があってもなくても）。FRAG のもとで $`\nu_S \ge X_{21}`$。$`\nu_C`$ より上での $`R_2^S`$ と $`R_2^C`$ の一致、
  $`\sigma_S \ge Z^\varepsilon`$、$`Z^\varepsilon`$ までの判定は節目に立っていたので、書いたままでは証明されていない。届く先を使わない結果は成り立つ：Carlson の範疇性 [C11] と MIN$`^S`$、型 K01、K2、
  CRIT-IND$`^K`$、UNIFORM-A（§2.2）。(E) は未解決で、$`\beta_0`$ の場所は分かっていない。
- **届く先**（FRAG のもと）：$`X_{21}`$ より下のどのやり直しでも、そして $`\hat G + G_2`$ より下のどの長い符号でもちょうど（TRANSLATION）。前のちょうどの長い式は $`m_0 \ge \Omega_1`$ と
  $`2 \le D \lt \hat G`$ で書いたとおりでは偽。上からの評価は成り立つ。
- **LOW と LOW$`^\infty`$：また決まっていない**（not-LOW と LOW$`^\infty`$ は $`\nu_C`$ への鎖に立っていた）。予想 CORE-2 の段階 PIN と LOW：決まっていない。
- **Lean**：$`R_2^C`$、同型最小の集合、核、LOC、FRAG、FRAG2（§3.3）。
- $`\theta_0`$ より下の下からの評価の計画：変化なし（$`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$、§2.3）。SRO より下の段階：変化なし（3,166 個の標本の行列すべてでどの $`n`$ でも。SRO より下の
  すべての標準の行列についての一般の命題は未解決）。

### 3.5 40 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §3.1。1 回の実行：証拠のやり直し（定義域に入ること、標準形、$`X_6`$ より下での順序）、失敗 0。査読者は探索をしなかった：いちばん弱い段階は留め、移し、数えることで、短い探索では
  確かめられない。
- §3.2。6 回の実行（小さい符号での直した値、境 $`\zeta_1`$、証拠、名前と順序 $`X_{18} \lt X_{19}^\flat \lt X_{19}^{\mathrm{lin}} \lt X_{19}`$）、失敗 0。査読者：$`[\hat\zeta_3, \zeta_{\mathrm{lin}})`$ の 2,512 個の正規の乗数を
  2 つの種で探し、境への反例 0。
- §3.3。Lean（`#eval` は無い）：9 個のファイルをまとめたものは緑、Mathlib だけを読む 2 つのファイルはそれだけでも緑。監査はまとめたものを作り直し（同じ）、38 個の定理の公理を表示して、
  書いたとおりだった。リポジトリでは 9 個のファイルがライブラリ全体とともにモジュールとして作られる（緑、`sorry` 無し）。
- §3.1 の著者は、迷い込んだシェルのコマンド 1 つを書き出した（影響なし）。

### 3.6 未解決

のちに：節目はもう一度証明された（[SHIFT11-ja.md](SHIFT11-ja.md) §1.1）。今の一覧は [SHIFT11-ja.md](SHIFT11-ja.md) §3.6 にある。

- 節目をもう一度、この順で：ENUM-REACH（$`P'`$ より下のどの符号でも直した値）、その移しでの不変性とその遠い留め。次に $`P'`$ より下の CAP-0、not-LOW、CAP-1、CROSS-LIM、TC⁺$`^\omega`$、EMB、
  ONTO-FIN、PAIR、UP、$`\nu_C = \nu_S = L(\omega+1)`$。次に $`\nu_C`$ より上の最前線（$`X_A`$ から $`Z^\Lambda`$）と $`R_2^S`$ の側。次に 1 つ上（定理 C$`^{\mathrm{LL}}`$、C$`^{\mathrm{FP}}`$、$`\nu_3`$）。
- FRAG のもとで $`R_2^C`$ で $`X_{21}`$ より上（FRAG 無しでは $`X_4`$ より上）、$`R_2^S`$ で $`\upsilon_{\omega^3}`$ より上の主張。
- Lean：$`R_2^C`$ の $`\le_1`$ と $`R_1^+`$ のつながり（INC1）、Carlson 2009, Thm 14.10 と 14.14、Lean の $`\upsilon`$ が Wilken のものであること。次に $`\upsilon_{\omega^3}`$ より下のブロック、やり直しのブロック、
  SKEL⁺、CAP、LIFT-0、O$`^C`$、NU-CT（[LEAN-ja.md](LEAN-ja.md)）。
- $`R_2^S = R_2^C`$：(E)、$`\beta_0`$（予想：$`\beta_0 \ge x_F^C`$）、FAN-LOAD、$`\kappa_C`$ より上の後続の段階での $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と $`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数：$`\varepsilon_{\Omega_\omega+1}`$ より先の鎖の数 3。$`S_*`$ より先は、$`\alpha \ge \Gamma_0`$ の容量（予想 LEX-SELF）か別のやり方。そのあと $`\theta_0`$ までの $`\Omega`$ の塔。
  $`\Theta_1`$ より先の $`\mathrm{CH}_2`$。SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。[COVER-ja.md](COVER-ja.md) §9 の残り。
