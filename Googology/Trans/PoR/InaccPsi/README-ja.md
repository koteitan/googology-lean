[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/PoR/InaccPsi: $`R_2^+`$ の核についての Wilken の主張

パターン → [InaccPsi](../../../Notation/InaccPsi/README-ja.md)（$`\omega`$ 個の弱到達不能基数の上の
Buchholz の $`\psi`$）の項。このディレクトリには、G. Wilken の主張についての作業を置く。主張が何を言うか、
何が証明済みか、何が未解決か、そして実験。

状態の言葉：**Lean**（Lean で検査済み。`sorry` なし。公理は `propext`、`Classical.choice`、`Quot.sound`
だけ）。**証明済み**（紙の上。独立した査読者が、致命的な点も止める点も無く証明済みと判定。2026-10 の印の結果は査読 1 回）。**引用**
（論文と場所）。**確認済み**（有限個の場合で計算）。**予想**。**未解決**。

## 1. 主張とその出典

G. Wilken, "A glimpse of Σ₃-elementarity" (2020), 420–421 ページ。G. Wilken, "Pure
Σ₂-elementarity beyond the core" (APAL 172, 2021), §1 でもくり返す：

> We claim that the segment of countable ordinals denoted by the Skolem-hull notation system
> derived from the first ω-many weakly inaccessible cardinals covers (the domain of) Core(R2+).

（最初の ω 個の弱到達不能基数から得られる Skolem 包の表記系が表す可算順序数の区間は、Core(R2+)
（の定義域）を覆う。）

ここで $`R_2^+ = (\mathrm{Ord}; 0, +, \le, \le_1, \le_2)`$、核はその有限パターンの最小の（isominimal な）
実現の合併。Wilken は続けて、弱到達不能基数 1 個の系は集合論 KPI の順序数に合うこと、$`R_2^+`$ の解析は
今後の仕事で、Weiermann–Wilken, "Ordinal arithmetic with simultaneously defined θ-functions"
(MLQ 57, 2011) で始めた算術が要ることを書く。2020 年の論文の 438 ページでは、$`R_2^+`$ の核が始切片であることを
「示す予定」と言う。手元の論文には、表記系の定義も証明も無い。

## 2. 正確な命題

この節は、主張の我々の読み方である。査読は無い。3 つのことを決める。

**(a)「覆う」の意味。** 同じ段落で Wilken は、$`R_1^+`$ と $`R_2`$ の核が「同じ始切片を覆う」、
つまりその切片そのものだと言う。だから一番強い読み方は集合の等式
$`\mathrm{Core}(R_2^+) = \rho`$。ここで $`\rho`$ は表記系の可算な値の集合。2 つの半分は、上界
$`\mathrm{Core}(R_2^+) \subseteq \rho`$ と下界 $`\rho \subseteq \mathrm{Core}(R_2^+)`$。

**(b) どの $`R_2^+`$ か。** Wilken は $`\le_i`$ を $`\Sigma_i`$ 初等性で定義する。これを $`R_2^S`$ と書く。
Carlson, "Patterns of resemblance of order 2" (APAL 158, 2009), Defs 5.3–5.4 は被覆で定義する。これを
$`R_2^C`$ と書く。両者が等しいことは $`\upsilon_{\omega\cdot\omega}`$ より下でしか示されていない
（[R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の定理 EQB）。これは $`\rho`$ のどの候補よりずっと下。
まず $`R_2^C`$ をとる。その核が始切片だと分かっているから：Carlson 2009, Thm 14.14 により、核は
「すべての $`\beta \ge \kappa`$ で $`\kappa \le_1 \beta`$」となる最小の $`\kappa`$。すると主張は、
すべての $`\beta \ge \rho`$ で $`\rho \le_1 \beta`$（上界）、かつ、それより小さい順序数はこの性質を持たない
（下界）、となる。$`R_2^S`$ は 2 番目。

**(c) どの表記系か。** 効くのは、つぶす関数の引数の上限 $`X`$。つぶす引数がすべて $`X`$ 未満の InaccPsi の
項の可算な値を $`\rho_X`$ と書く。候補は 3 つ：

| 読み方 | 上限 | 可算な部分 |
|---|---|---|
| A（第一） | $`I_\omega`$ | $`\rho_A = \psi_{\Omega_1}(I_\omega)`$ |
| B | $`\varepsilon_{I_\omega+1}`$ | $`\rho_B = \psi_{\Omega_1}(\varepsilon_{I_\omega+1})`$ |
| S（系全体） | なし | $`\rho_S = \psi_{\Omega_1}(\Lambda)`$。$`\Lambda`$ は $`\Omega_\alpha = \alpha`$ となる $`I_\omega`$ より大きい最小の $`\alpha`$ |

Lean で $`\rho_A \lt \rho_B \lt \rho_S`$ を証明した。だから等式で成り立つ読み方は多くても 1 つ。A を第一に
とる：Wilken 自身の系 $`T^\tau`$ は有限の段の系の合併で、その可算な部分は上限をつぶしたもの。また
$`\sup_k \psi_{\Omega_1}(I_k) = \sup_k \psi_{\Omega_1}(\varepsilon_{I_k+1}) = \psi_{\Omega_1}(I_\omega)`$
（連続性、下の補題 CONT）なので、A は KPI についての注意にも合う。ほかの標準的な系が同じ上限で同じ可算順序数を
与えることは予想。

まとめると、主な命題は（$`R_2^C`$、読み方 A）：

```math
\mathrm{Core}(R_2^C) = \psi_{\Omega_1}(I_\omega) = \{\, |t| : t \text{ an InaccPsi normal form, all collapse arguments } \lt I_\omega,\ |t| \lt \Omega_1 \,\}.
```

どちらの半分も**未解決**。$`\upsilon_{\omega\cdot\omega}`$ より下では両方とも成り立つ（§3）。

## 3. 証明済みのこと

**まとめ。** $`\upsilon_{\omega\cdot\omega}`$ より下では、主張は $`R_2^C`$ でも $`R_2^S`$ でも成り立つ：$`\upsilon_{\omega\cdot\omega}`$ 未満の
どの順序数も核に入り、しかも、つぶす引数がすべて $`I_\omega`$ 未満の InaccPsi の標準形の可算な値である（下の定理 LOW）。
$`\upsilon_{\omega\cdot\omega}`$ より上では、どちらの半分も未解決。

**Lean**（このディレクトリの 4 つのファイル。ライブラリ全体と一緒にビルドした）：

- **補題 L**（`CSet_inter_Om1`）。どの $`\alpha`$ でも、集合として $`\mathrm{Cl}(\alpha, 0) \cap \Omega_1 = \psi_{\Omega_1}(\alpha)`$。
  だから $`X`$ で上を抑えた項の可算な値は、ちょうど $`\psi_{\Omega_1}(X)`$ 未満の順序数
  （`bounded_inter_Om1`）。系全体なら $`\psi_{\Omega_1}(\Lambda)`$ 未満の順序数（`vals_inter_Om1`、
  `CSet_sub_Lam`）。どれも $`\Omega_1`$ の始切片。
- **3 つの上限**（`three_bounds`）。$`\rho_A \lt \rho_B \lt \rho_S`$。
- **補題 IS**（`lt_psi_one_mem_Vals`、`exists_NF_of_lt_psi_one`、`mem_Vals_of_lt_of_countable`）。
  $`\psi_{\Omega_1}(a)`$ 未満のどの順序数も、ある標準形の値。可算な値は下に閉じている。証明の考え：値でない最小の
  $`\rho`$ は $`+`$ と $`\varphi`$ で閉じ、どの $`\psi_{\Omega_1}(a)`$ の定義の条件も満たす。
- **補題 CONT**（`psi_one_iSup`）。増加列 $`a_n`$ で $`\psi_{\Omega_1}(\sup_n a_n) = \sup_n \psi_{\Omega_1}(a_n)`$。
- **7 つの項**（`LowTerms.lean`）。$`\eta \in \{0, 1, 2, \omega, \omega+1, \omega\cdot 2, \omega^2\}`$ で、項
  $`u(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$（$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$）は標準形で、
  この値を持ち、7 つの値は増える。また $`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$。
- **定理 T-UP の InaccPsi 側**（`ConjT.lean`）。$`A_\eta = \Omega_\omega + \theta\cdot\eta`$ とする。定理 STEP の仮定 (HA) は
  $`A_\eta`$（$`\eta \lt \omega^2`$）で成り立つ（`HA_A`）。出発点 $`u(1) \le \psi_{\Omega_1}(\Omega_\omega)`$、定理 STEP の段、極限での
  連続性を満たすどの関数 $`u`$ でも、$`\eta \le \omega^2`$ で $`u(1+\eta) \le \psi_{\Omega_1}(A_\eta)`$（`upper_bound`、
  `upper_bound_ww`）。$`u(\omega^2)`$ 未満のどの順序数も標準形の値（`conjU`）。補題 M で使う順序数の算術 2 つ
  （`arith_absorb`、`arith_lex`）。Wilken の $`\upsilon`$、彼の系、写像 $`B`$ は Lean に無い：段は仮定であり、
  Lean はそれを $`\xi = 0`$ でも仮定する。紙の上では自明だが、Lean では確かめていない。

**紙の上で証明し、査読済み。** (2026-10) の印の項目は、それぞれ反論を試みる査読を 1 回受け、致命的な点も
止める点も無かった。それらの査読で止める点は 1 つだけで、下界の未解決の穴（「証明されていないこと」に書く）。

**$`\upsilon_{\omega\cdot\omega}`$ より下。**

- **定理 CORE-C。** $`\upsilon_{\omega\cdot\omega}`$ 未満の順序数はどれも $`\mathrm{Core}(R_2^C)`$ に入る。証明：定理 EQB の
  上限により、$`\alpha \lt \upsilon_{\omega\cdot\omega}`$ はどれも、上のすべてに $`\le_1`$ ではない。Carlson 2009,
  Thm 14.14 により、核はそういう最小の順序数（または Ord 全体）。
- **補題 RESTR。** $`\Omega_\omega`$ より下では、InaccPsi の包と、到達不能基数 1 個の Pohlers の系（Pohlers,
  "Subsystems of set theory and second order number theory", Handbook of Proof Theory 1998,
  Def 3.4.4.1）の包は一致し、$`\psi_{\Omega_{n+1}}`$ も一致する。引用した $`\mathrm{ID}_{\lt\omega}`$ の順序数
  （Wilken 2021, §1。Pohlers 1998, Fig. 1）と合わせて $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$
  （引用、間接）。文献の中に弱い所が 2 つある：Pohlers は再帰的正則順序数を正則基数に置き換えることを証明なしに
  行う。Wilken は $`\mathrm{ID}_{\lt\omega}`$ の順序数を証明なしに述べる。上半分
  $`\upsilon_1 \le \psi_{\Omega_1}(\Omega_\omega)`$ は、下の定理 STEP-0 で直接出るようになった。
- $`\psi_{\Omega_1}(0) = \Gamma_0`$、$`\vartheta_0(\varepsilon_{\Omega+1}) = \psi_{\Omega_1}(\varepsilon_{\Omega_1+1})`$（引用 + RESTR）。
- **定理 MAIN。** 次は同値：(i) $`\upsilon_{\omega\cdot\omega}`$ 未満の $`\mathrm{Core}(R_2^C)`$ の順序数はどれも可算な
  InaccPsi の項の値。(ii) $`\upsilon_{\omega\cdot\omega}`$ 未満の順序数はどれもそう。(iii) **予想 U**：
  $`\upsilon_{\omega\cdot\omega} \le D`$。ここで $`D = \sup_a \psi_{\Omega_1}(a)`$。証明：CORE-C と補題 IS。
- **定理 STEP**（2026-10）。Wilken の点：$`\upsilon_0 = 0`$、$`\upsilon_{\xi+1} = T^{\upsilon_\xi} \cap \Omega_1`$、極限では上限
  （Wilken 2020, Def 21.4。$`\upsilon_1 = T^1 \cap \Omega_1`$ は 420 ページ）。$`\tau`$ を $`1`$ か $`\varepsilon`$ 数とし、
  $`\Omega_\omega \le A`$、$`\tau \le \psi_{\Omega_1}(A)`$、(HA) $`A \in \mathrm{Cl}(A+1, \psi_{\Omega_1}(A))`$ とする。すると
  $`T^\tau \cap \Omega_1 \le \psi_{\Omega_1}(A + \theta)`$。ここで $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$。
  **STEP-0**：$`\upsilon_1 \le \psi_{\Omega_1}(\Omega_\omega)`$。証明論の引用を使わない。
  証明の筋。Weiermann–Wilken 2011 の Def 3.9 と Cor 3.7(f) から、Wilken の段ごとの系 $`T^\tau`$ と同時に定義した系
  $`\bar T^\tau`$ は同じ集合（補題 SAME-SET）。$`\bar T^\tau`$ には定義域の規則（そこの Lemma 4.3）と比較の規則
  （そこの Lemma 4.4）がある。$`\bar T^\tau`$ から InaccPsi への写像 $`B`$ は、$`\bar\vartheta_i(\alpha)`$ を
  $`\psi_{\Omega_{i+1}}(X_i + c_i(\alpha) + \mathrm{code}_i(\alpha))`$ に送る。ここで $`X_0 = A`$、$`i \ge 1`$ で $`X_i = 0`$、
  $`i \ge 1`$ で $`\mathrm{code}_i(\alpha) = \omega^{B(\alpha)}`$、$`\mathrm{code}_0(\alpha) = \psi_{\Omega_2}(\omega^{B(\alpha)}) \lt \theta`$。
  $`c_i(\alpha)`$ は、引数を $`\alpha`$ の段 $`i`$ の最大のパラメータの像の引数より上に持ち上げる。補題 N：像の引数は
  それぞれ自分の包に入る。補題 M：$`B`$ は狭義に増加。だから $`T^\tau \cap \Omega_1 \le \sup B \le \psi_{\Omega_1}(A+\theta)`$。
  証明を支える新しい補題は SAME-SET、N、N2、M。
- **定理 T-UP**（2026-10）。どの $`\eta \lt \Gamma_0`$ でも $`\upsilon_{1+\eta} \le \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$。
  証明：STEP で帰納法。極限は補題 CONT。$`\eta = \omega^2`$ までの帰納法は Lean にある（`ConjT.lean`）。
- **予想 U は証明された**（2026-10）：$`\upsilon_{\omega\cdot\omega} \le \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+2}) \lt D`$。MAIN により、
  $`\upsilon_{\omega\cdot\omega}`$ 未満のどの順序数も可算な InaccPsi の標準形の値で、つぶす引数は
  $`\Omega_\omega + \omega^{\theta+2} \lt I_\omega`$ 未満（補題 L）。
- **定理 CORE-S**（2026-10）。$`\upsilon_{\omega\cdot\omega}`$ 未満のどの順序数も $`\mathrm{Core}(R_2^S)`$ に入る。補題 FRAG を
  仮定すれば $`\upsilon_{\omega^3}`$ 未満のどれも。$`\upsilon_{\omega\cdot\omega}`$ より下では、$`R_2^S`$ の最小の閉じた集合は、
  ちょうど $`R_2^C`$ の isominimal な集合。要の段は補題 FOLD：$`f`$ が被覆なら、$`f`$ と恒等写像の各点ごとの最小も
  被覆。ただし $`\lt_2`$ の組が入れ子にならないこと。補題 NEST：長さ 3 の鎖より上では、この条件は成り立たない。
  ここで $`R_2^S`$ での「最小」は Wilken の定義（2021, 6 ページ。+ の無い $`R_2`$ のもの）を $`R_2^+`$ に読んだもの。
- **定理 LOW**（上のまとめ）は、CORE-C、CORE-S、予想 U、補題 L から出る。

**$`R_2^S`$ と $`R_2^C`$**（2026-10）。2 つの構造で、ある関係 $`\alpha \le_i \beta`$ が食い違う最小の段 $`\beta`$ を
$`\beta_0`$ とする（等しければ $`\beta_0 = \infty`$）。$`\beta \ge \kappa`$ のすべてで $`\kappa \le_1^X \beta`$ となる最小の $`\kappa`$ を $`\kappa_X`$ とする。

- **補題 STAGE。** $`\beta`$ より下のすべての組で 2 つの構造が一致するなら、$`\alpha \le_1^S \beta \Rightarrow \alpha \le_1^C \beta`$。
  さらに $`\beta`$ への $`\le_1`$ も一致するなら、$`\alpha \le_2^S \beta \Rightarrow \alpha \le_2^C \beta`$。道具：有限集合による判定
  （下の T1）、定理 EQ の先頭の項への置き換え、Wilken 2021 の Lemma 1.7(2) の $`R_2^+`$ 版、$`\Pi_2`$ 文の移し。
- **系 FIRST。** 右端が $`\beta_0`$ 未満の $`R_2^S`$ の関係、および右端が $`\beta_0`$ の $`\le_1^S`$ の関係は、どれも $`R_2^C`$ で
  成り立つ。$`\beta_0`$ での食い違いは、$`R_2^C`$ の余分な関係。だから $`R_2^S = R_2^C`$ は、一致する段のすべてで逆向き
  （$`C \Rightarrow S`$）が成り立つことと同値。また $`\beta_0 \gt \upsilon_{\omega\cdot\omega}`$、FRAG を仮定すれば
  $`\beta_0 \ge \upsilon_{\omega^3}`$、$`\beta_0`$ は可算か $`\infty`$。
- **補題 UPG。** 一致する段では、$`\alpha`$ 未満のどの $`\gamma`$ も $`R_2^C`$ で $`\alpha`$ の isominimal な部分集合に入るなら、
  $`\alpha \le_1^C \beta \Rightarrow \alpha \le_1^S \beta`$（$`\alpha = \kappa_C`$ と $`\alpha = \upsilon_{\omega\cdot\omega}`$ で成り立つ）。
- **KAPPA と CORE-EQ。** $`\kappa_C \le \beta_0 \Rightarrow \kappa_C \le \kappa_S`$、$`\kappa_S \le \beta_0 \Rightarrow \kappa_S \le \kappa_C`$。だから
  $`\max(\kappa_S, \kappa_C) \le \beta_0`$（AGR と呼ぶ）なら $`\mathrm{Core}(R_2^S) = \mathrm{Core}(R_2^C)`$。$`R_2^C`$ での主張と AGR から、
  $`R_2^S`$ での主張が出る。

**$`R_2^S`$ での有限集合による判定**（2026-10）。言語 $`\{0, +, \le, \le_1, \le_2\}`$ を有限の関係の言語として読む。

- **T1**（$`\Sigma_1`$）。$`\alpha \le_1 \beta`$ は次と同値：有限の $`X \subset \alpha`$ と $`Y \subset [\alpha, \beta)`$ のどれにも、
  $`X \lt \tilde Y`$ となる $`\tilde Y \subset \alpha`$ と、$`X`$ を動かさない同型 $`X \cup \tilde Y \cong X \cup Y`$ がある。
  $`\tilde Y`$ は、どの $`\rho \lt \alpha`$ より上にもとれる。
- **補題 PR。** $`\alpha \lt_1 \beta`$ なら $`\alpha = \omega^a`$（$`a`$ は極限）。$`\alpha \lt_2 \beta`$ なら $`\beta = \omega^\lambda`$
  （$`\lambda`$ は極限）で、$`\alpha`$ はその $`\lt_1`$ の前の元たちの上限。
- **T2**（$`\Sigma_2`$、段つきの形。「同値」である。Wilken 2021 の Prop 1.6 と Wilken 2020 の Prop 21.11 は片向き
  だけ）。$`\alpha \le_2 \beta`$ は次と同値：そういう $`X, Y`$ とどの $`k`$ にも、T1 のような写し $`\tilde Y`$ があって、
  $`\alpha`$ 未満の $`k`$ 個以下の点でのどの拡張も、同型を $`\beta`$ の中へ延ばす。写しは、さらに共終に、
  $`y \le_1 \beta \Leftrightarrow \tilde y \le_1 \alpha`$ となるように、$`X \cup Y`$ が閉じていれば閉じるように、とれる。
- **定理 CMP。** $`\alpha \le_i^S \beta`$ なら、$`R_2^S`$ の中で計算した Carlson の被覆の条件が $`\le_i`$（$`i = 1, 2`$）で成り立つ。
  Carlson 2009, 98 ページは、これを証明なしに予告する。補題 KEEP：先頭の項への置き換えは、前向きの $`\le_1`$ と
  $`\le_2`$ を保つ。$`\lt_2`$ の組の両端は加法的主要数だから。

**鎖。** 長さ $`n`$ の鎖は、互いに $`\le_2`$ な $`n`$ 個の加法的主要数。$`C^*_n`$ は各点ごとに最小のもの。

- **定理 CC**（$`R_2^C`$ で）。$`\mathrm{Core}(R_2^C) = \sup_n \max C^*_n`$。加法的主要数を $`n`$ 個持つパターンの最小の実現は
  $`\max C^*_{n+1}`$ より下。（$`R_2^S`$ では未解決。AGR があれば核は同じ。）
- **定理 DOM₂**（2026-10、$`R_2^C`$）。$`C^*_3 = \{c_0 \lt c_1 \lt c_2\}`$、$`m_3 = \min\{m : m \le_1 c_0\}`$ とする。長さ 3 の鎖を
  持たないパターンの最小の実現は $`m_3`$ より下で、$`m_3 \lt c_0`$。**定理 SHARP**：長さ 3 の鎖を持たない isominimal な
  集合の合併は、ちょうど $`[0, m_3)`$。**DOM₁′**：$`\lt_2`$ の組を持たないパターンで同じこと。その合併は $`[0, m_2)`$、
  $`m_2`$ は $`\min C^*_2 = \upsilon_\omega`$ の最小の $`\le_1`$ の前の元。引用した $`R_1^+`$ の核と定理 A・EQ を仮定すれば
  $`m_2 = \upsilon_1`$。
- $`C^*_3`$ についての事実（2026-10）：$`[0, c_2)`$ の中に長さ 3 の鎖は無い。$`c_0`$ はその $`\lt_1`$ の前の元たちの極限。
  FRAG を仮定すれば $`m_3 \ge \upsilon_{\omega^3}`$。以前から：$`C^*_2 = \{\upsilon_\omega, \upsilon_{\omega+1}\}`$。
- 小さな補題：**PRINC**（$`x \lt_1 y`$ なら $`x`$ は加法的主要数。$`x \lt_2 y`$ なら $`y`$ は加法的主要数）、
  **ISO-UNION**（isominimal な集合の有限個の合併は isominimal）、**HULL**（非可算な正則基数 $`\kappa`$ は、上の
  すべてに $`\le_1`$。両方の構造で）、**DOM₁**（$`\lt_2`$ の組を持たないパターンの最小の実現は $`\upsilon_1`$ より下）。

**下界に向けて**（2026-10、$`R_2^C`$）。$`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$ と書く。

- **補題 I-FREE。** 可算な標準形が到達不能基数の記号を含まないことと、その値が $`\theta_0`$ 未満であることは同値。
  だから到達不能基数を使わない項は、ちょうど $`\theta_0 \lt \psi_{\Omega_1}(I_0)`$ 未満の項。
- **補題 OE。** $`\gamma`$ 未満の標準形から点つきパターンへの写像 $`F`$ で、「$`F(t)`$ の最小の実現の点」が $`t`$ について
  狭義に増加するものがあれば、$`[0, \gamma) \subseteq \mathrm{Core}(R_2^C)`$。**EPS-RED**：$`F`$ は値が $`\varepsilon`$ 数の項でだけ
  要る。**FS-OE**：狭義の増加は 2 つの局所的な段「前の項は $`t`$ より下」「$`t[n]`$ は $`t`$ より下」から出る。
- **RED-BMS。** [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の定理 S と合わせると、$`\gamma`$ より下の下界は、
  $`\gamma`$ 未満の $`\varepsilon`$ 数の項から $`V`$ 未満（FRAG を仮定すれば $`V_3`$ 未満）の標準形のトリオ行列への順序を保つ
  埋め込み $`\mu`$ から出る。**S-RED**：Lean のクラス `TrioStdL` の行列では、$`\Phi_3`$ の点の狭義の増加は、ただ 1 つの命題
  「どの $`A`$ と $`k`$ でも $`\Phi_3(A[k])`$ の点は $`\Phi_3(A)`$ の点より下」に帰着する（Lean の定理 `trio_fs` と BMS の停止性から）。
- **補題 MU-A。** 項の断片 $`G_A`$（和。$`\Omega_\omega`$、$`\omega^{\Omega_\omega + c}`$、$`\theta\cdot\omega^e`$ の和の $`\psi_{\Omega_1}`$）の上で、
  トリオ行列への再帰的な写像 $`\mu`$ は狭義に増加。
- **補題 UNIF-V。** $`A_m = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)^m`$（$`m \ge 3`$）とどの $`N`$ でも、$`\Phi_3(A_m[N])`$ の点は
  $`\Phi_3(A_m)`$ の点より下。$`\Phi_3`$ の出力の形を仮定する（$`m \le 8`$、$`N \le 6`$ で確認済み）。R2PLUS の定理 V
  （$`m = 2`$）を広げる。

**証明されていないこと：**

- **予想 T そのもの**（正確な名前、§4）：$`\eta \ge 1`$ での下半分 $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) \le \upsilon_{1+\eta}`$。
  InaccPsi の値から Wilken の $`\bar T^\sigma`$ への逆向きの埋め込みが要る。$`\eta = 0`$ の等式は RESTR の間接的な引用だけ。
- **$`\upsilon_{\omega\cdot\omega}`$ より上での主張**、両方の半分。
- **$`R_2^S = R_2^C`$**：逆向き $`C \Rightarrow S`$（$`\le_2`$ と、UPG の外の $`\le_1`$）、$`\beta_0`$ より先での包含
  $`S \subseteq C`$、AGR。定理 CC とすべての証明書は $`R_2^C`$ の話。
- **$`\theta_0`$ より下の下界**（査読：この目標に向けた止める穴。本文の誤りではない）：$`\theta_0`$ 未満のすべての
  $`\varepsilon`$ 数の項から SRO 未満の標準形のトリオ行列への順序を保つ埋め込み $`\mu`$ と、SRO 未満のすべての行列での
  S-RED の局所的な段。その先に区間 $`[\theta_0, \psi_{\Omega_1}(I_0))`$ があり、$`\psi_{I_0}`$ でつぶす項が要る。
- **$`C^*_3`$ を具体的に。** 予想（+ の無い $`R_2`$ での Wilken の最小の 3 鎖、2021, 19–21 ページ、と CH から）。
  $`P = \psi_{\Omega_2}(\Omega_\omega)`$、$`E = \varepsilon_{I_0+1}`$ として $`m_3 = \psi_{\Omega_1}(E)`$、
  $`C^*_3 = \{\psi_{\Omega_1}(E + \Omega_\omega),\ \psi_{\Omega_1}(E + \Omega_\omega + \omega^{P+1}),\ \psi_{\Omega_1}(E + \Omega_\omega + \omega^{P+1} + P)\}`$。
  どれも標準形で、$`\psi_{\Omega_1}(I_0)`$ と $`\psi_{\Omega_1}(I_1)`$ の間にある（Python と Lean で確認済み）。
- $`\Phi_3`$ が長さ 3 の鎖を作らないこと（確認済みだけ）。これがあれば、DOM₂ により $`\Phi_3`$ のどの点も $`m_3`$ より下。

## 4. Wilken の点の名前（予想 T）

**予想 T。** $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$ として、$`\eta \le \omega^2`$ で：

```math
\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta).
```

上半分「$`\le`$」は、すべての $`\eta \lt \Gamma_0`$ で証明済み（定理 T-UP）。下半分は $`\eta \ge 1`$ で未解決。
$`\eta = 0`$ では引用（RESTR）。

| $`\eta`$ | 点 | 項 |
|---|---|---|
| $`0`$ | $`\upsilon_1`$ | $`\psi_{\Omega_1}(\Omega_\omega)`$（引用） |
| $`1`$ | $`\upsilon_2`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta)`$ |
| $`2`$ | $`\upsilon_3`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot 2)`$ |
| $`\omega`$ | $`\upsilon_\omega`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1})`$ |
| $`\omega+1`$ | $`\upsilon_{\omega+1}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1} + \theta)`$ |
| $`\omega\cdot 2`$ | $`\upsilon_{\omega\cdot 2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1}\cdot 2)`$ |
| $`\omega^2`$ | $`\upsilon_{\omega^2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+2})`$ |

出てくるのは $`\psi_{\Omega_1}`$、$`\psi_{\Omega_2}`$、$`\Omega_\omega`$ だけ。$`\upsilon_{\omega\cdot\omega}`$ より下では到達不能基数は
要らない。予想 T が正しければ、素朴な予想 $`\upsilon_\iota = \psi_{\Omega_1}(\Omega_\omega\cdot\iota)`$ は $`\iota = 2`$ から
大きすぎる（Lean：$`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$）。$`+\theta`$ の理由：STEP の証明で、段 0 の符号
$`\mathrm{code}_0`$ は $`\theta`$ より下にとどまる。下半分の根拠：[R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の翻訳
`por/tr3.py` は、定理 S の行列でこれらの点を与える（確認済み）。

## 5. 道筋：補題の木

道は 3 つ：B は上界、A は全部の解析、L は下界。

- **W** Wilken の主張、$`\mathrm{Core}(R_2^+) = \psi_{\Omega_1}(I_\omega)`$ — 未解決
  - **Low** $`\upsilon_{\omega\cdot\omega}`$ より下、$`R_2^C`$ と $`R_2^S`$ で — 証明済み（定理 LOW）
    - 予想 U — 証明済み（STEP、T-UP）
    - 予想 T、正確な名前 — 上半分は証明済み。下半分は未解決（$`\bar T^\sigma`$ への逆向きの埋め込み）
    - $`\mathrm{Core}(R_2^S)`$ が $`\upsilon_{\omega\cdot\omega}`$ 全体を含む — 証明済み（CORE-S）
  - **B** 上界 $`\mathrm{Core}(R_2^+) \subseteq \psi_{\Omega_1}(I_\omega)`$ — 未解決
    - B0 最小の鎖への帰着（定理 CC） — $`R_2^C`$ で証明済み
      - B0-S $`R_2^S`$ で同じこと — 未解決。AGR から出る
        - $`S \Rightarrow C`$ — $`\beta_0`$ まで証明済み（STAGE、FIRST）。$`\beta_0`$ より先は未解決（それだけでは帰納法にならない）
        - 一致する段での $`C \Rightarrow S`$ — $`\le_1`$ は UPG の仮定の下で証明済み。$`\le_2`$ とほかの $`\alpha`$ は未解決
    - B1 どの長さ $`n`$ でも、$`\psi_{\Omega_1}(I_\omega)`$ より下の鎖を InaccPsi の値で具体的に書く — 未解決
      （$`n = 3`$ の予想は §3）
    - B2 $`R_2^+`$ での $`\lt_2`$ の有限集合による判定 — 証明済み（T1、T2）。一様な形（すべての $`k`$ に 1 つの写し）が
      必要条件でもあるかは $`R_2^+`$ で未解決（+ の無い $`R_2`$ では成り立つと Wilken 2021, 6 ページが言う）
    - B3 $`0, +, \le, \le_1, \le_2`$ を保つ基の付け替え（補題 FRAG を $`\le_2`$ に広げる）。B4 と一緒に証明する
      — 未解決、とても難しい
    - B4 B3 が動かす点の間の $`\le_2`$ の組 — 未解決、とても難しい
    - B5 B2 + B3 + B4 を組み立てる — 形だけ
    - B-PT 証明論の別の道：到達不能基数 $`n`$ 個の理論が「長さ $`n`$ の鎖がある」を証明する — 未解決。
      $`\lt_2`$ の集合論的な十分条件が要るが、知られていない
  - **A** 全部の解析 — 未解決
    - A1 どの基の上でも、すべての $`\Omega_\xi`$ と $`I_n`$ のつぶす関数を同時に定義した包の系を作り、InaccPsi と比べる
      — 未解決、難しい（STEP の写像 $`B`$ が、$`\Omega_\omega`$ より下で片向きにこれをする）
    - A2 上限までの $`R_2^+`$ の $`\le_1`$、$`\le_2`$ の構造定理（Wilken 2021, Thm 4.2 の類似）。
      [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の結果は、$`\upsilon_{\omega^3}`$ より下でのこの定理 — 未解決、
      とても難しい
    - A3 最小の実現を項で書く — 未解決
    - A4 **予想 CH**：長さ $`k+2`$ の最小の鎖には到達不能基数が $`k`$ 個要る — 予想
    - A5 上限より下のどの項も、あるパターンの値 — 未解決
    - A6 どこでも $`R_2^S = R_2^C`$ — 未解決（$`\beta_0 \gt \upsilon_{\omega\cdot\omega}`$ より下では一致）
  - **L** 下界 $`\psi_{\Omega_1}(I_\omega) \subseteq \mathrm{Core}(R_2^+)`$ — 未解決
    - L0 $`R_2^C`$ では「どの $`\gamma \lt \psi_{\Omega_1}(I_\omega)`$ も、ある $`\max C^*_n`$ より下」と同値 — 証明済み
    - L-CERT $`\theta_0`$ より下：帰着は証明済み（I-FREE、OE、EPS-RED、FS-OE、RED-BMS、S-RED、MU-A、UNIF-V）。
      残り：$`\theta_0`$ 未満のすべての $`\varepsilon`$ 数の項の埋め込み $`\mu`$ と、SRO 未満での局所的な段 — 未解決
    - L-CERT $`[\theta_0, \psi_{\Omega_1}(I_0))`$ とその上 — 未解決
    - L-BMS $`\Phi_3`$ を通す道 — 止まっている：DOM₂ により、長さ 3 の鎖の無い $`\Phi_3`$ のパターンは $`m_3`$ より下にとどまり、
      調べた $`\Phi_3`$ のパターンにそういう鎖は無い（§6）
  - **わきの葉**
    - **DOM₂** — 証明済み（SHARP も）。どの $`k`$ でも DOM$`_k`$ — 予想
    - $`C^*_3`$ の場所を見つける — 未解決（予想は §3。分かっていること：FRAG を仮定すれば $`m_3 \ge \upsilon_{\omega^3}`$）
    - Lean：上を抑えた項の順序型が $`\psi_{\Omega_1}(X)`$ であること。補題 LOC（有限集合が isominimal かどうかは、
      その最大の元までの構造だけで決まる。紙の上、査読なし） — 未解決

## 6. 実験

すべて確認済みか予想。ここには証明は無い。どの実行も 60 秒未満。

**道具。** InaccPsi の比較、`KLt`、`NF` を Python に移したものは、Lean の `Term.cmp` とランダムな 600 組の
600 組で一致し、`NF` とは 120 項の 120 項で一致する。トリオ行列 $`M`$ は 3 つのプログラムで読む：
`por/tr3.py`（Wilken の $`\upsilon_\iota`$ と $`T^\tau`$ の項）、Ytosk のアルゴリズム（2020、トリオ行列 →
拡張ブーフホルツ $`\psi`$、SRO より下で有効。
[ブログ記事](https://googology.fandom.com/wiki/User_blog:Ytosk/Algorithm_that_changes_BMS_matrices_into_ordinals_up_to_SRO)、
実行だけ）、"BMS analyzer Mk. II"（実行だけ）。$`M`$ のパターンは `por/phi3def2.py` の $`\Phi_3(M)`$。
パターンの間の「$`\lt`$」は Carlson の規則の証明書で示す。

**表**（$`\Phi_3(M)`$ の最小の実現の、予想した項 $`J`$）。表の中で、`p0(a)` は $`\psi_{\Omega_1}(a)`$、
`p1(a)` は $`\psi_{\Omega_2}(a)`$、`pI0(a)` は $`\psi_{I_0}(a)`$、`W` は $`\Omega_1`$、`W_a` は $`\Omega_a`$、`w` は
$`\omega`$、`w^x` は $`\omega^x`$、`P` は `p1(W_w)`、`t6` は 6 行目の項。行列：`Z` = (0,0,0)(1,1,1)、`K` =
(1,1,0)(2,2,1)。値の状態：「証明」= $`V`$ より下の定理 S。「FRAG」= FRAG を仮定した $`V_3`$ より下の定理 S。
「数値」= 数値で確かめただけ。一致：同じ $`J`$ に変換される読み方。

| # | 名前 | M | J | 値 | 一致 |
|---|---|---|---|---|---|
| 1 | υ₁ | `Z` | `p0(W_w)` | 引用 | tr3, Ytosk |
| 2 | υ₂ | `Z K` | `p0(W_w+P)` | 証明 | tr3, Ytosk |
| 3 | υ_ω | `Z K (2,0,0)` | `p0(W_w+w^(P+1))` | 証明 | tr3, Ytosk |
| 4 | U = υ_{ω+1} | `Z K (2,0,0) K` | `p0(W_w+w^(P+1)+P)` | 証明 | tr3, Ytosk |
| 5 | V₂ = υ_{ω·2+1} | `Z K (2,0,0) K (2,0,0) K` | `p0(W_w+w^(P+1)·2+P)` | 証明 | tr3, Ytosk |
| 6 | V = υ_{ω²} | `Z K (2,0,0)(2,0,0)` | `p0(W_w+w^(P+2))` | FRAG | tr3, Ytosk |
| 7 | V+1 | `V (1,0,0)` | `w^(t6+1)` | FRAG | tr3 |
| 8 | V の後の ε | `V (1,1,0)` | `phi(1,t6+1)` | FRAG | tr3 |
| 9 | V の後の φ₂ | `V (1,1,0)(2,1,0)` | `phi(2,t6+1)` | FRAG | tr3 |
| 10 | V の後の BHO | `V (1,1,0)(2,2,0)` | `p0(W_w+w^(P+2)+phi(1,W+1))` | FRAG | tr3 |
| 11 | υ_{ω²+1} | `Z K (2,0,0)(2,0,0) K` | `p0(W_w+w^(P+2)+P)` | FRAG | tr3, Ytosk |
| 12 | υ_{ω²+ω} | `Z K (2,0,0)(2,0,0) K (2,0,0)` | `p0(W_w+w^(P+2)+w^(P+1))` | FRAG | tr3, Ytosk |
| 13 | υ_{ω²+ω+1} | `Z K (2,0,0)(2,0,0) K (2,0,0) K` | `p0(W_w+w^(P+2)+w^(P+1)+P)` | FRAG | tr3, Ytosk |
| 14 | υ_{ω²·2} | `Z K (2,0,0)(2,0,0) K (2,0,0)(2,0,0)` | `p0(W_w+w^(P+2)·2)` | FRAG | tr3, Ytosk |
| 15 | V₃ = υ_{ω³} | `Z K (2,0,0)(2,0,0)(2,0,0)` | `p0(W_w+w^(P+3))` | 数値 | tr3, Ytosk |
| 16 | υ_{ω³+1} | `V₃ K` | `p0(W_w+w^(P+3)+P)` | 数値 | tr3, Ytosk |
| 17 | υ_{ω⁴} | `Z K (2,0,0)(2,0,0)(2,0,0)(2,0,0)` | `p0(W_w+w^(P+4))` | 数値 | tr3, Ytosk |
| 18 | υ_{ω^ω} | `Z K (2,0,0)(3,0,0)` | `p0(W_w+w^(P+w))` | 数値 | tr3, Ytosk |
| 19 | 18 行目の後の BHO | `Z K (2,0,0)(3,0,0)(1,1,0)(2,2,0)` | `p0(W_w+w^(P+w)+phi(1,W+1))` | 数値 | tr3 |
| 20 | υ_{ω^ω+1} | `Z K (2,0,0)(3,0,0) K` | `p0(W_w+w^(P+w)+P)` | 数値 | tr3, Ytosk |
| 21 | υ_{ω^ω^ω} | `Z K (2,0,0)(3,0,0)(4,0,0)` | `p0(W_w+w^(P+w^w))` | 数値 | tr3, Ytosk |
| 22 | υ_{ε₀} | `Z K (2,0,0)(3,1,0)` | `p0(W_w+w^(P+eps0))` | 数値 | tr3, Ytosk |
| 23 | υ_{ε₀+1} | `Z K (2,0,0)(3,1,0) K` | `p0(W_w+w^(P+eps0)+P)` | 数値 | tr3, Ytosk |
| 24 | BHO での υ | `Z K (2,0,0)(3,1,0)(4,2,0)` | `p0(W_w+w^(P+p0(phi(1,W+1))))` | 数値 | tr3, Ytosk |
| 25 | υ₁ での υ | `Z K (2,0,0)(3,1,1)` | `p0(W_w+w^(P+p0(W_w)))` | 数値 | tr3, Ytosk |
| 26 | υ の最初の不動点 | `Z K (2,1,0)` | `p0(W_w+w^(P+W))` | 数値 | Ytosk |
| 27 | | `Z (1,1,1)` | `p0(W_w·2)` | 数値 | Ytosk |
| 28 | | `Z (2,0,0)` | `p0(w^(W_w+1))` | 数値 | Ytosk |
| 29 | | `Z (2,1,0)` | `p0(w^(W_w+W))` | 数値 | Ytosk |
| 30 | | `Z (2,1,0)(3,2,0)` | `p0(phi(1,W_w+1))` | 数値 | Ytosk |
| 31 | | `Z (2,1,0)(3,2,1)` | `p0(W_(w·2))` | 数値 | Ytosk |
| 32 | | `Z (2,1,1)` | `p0(W_(w^2))` | 数値 | Ytosk |
| 33 | | `Z (2,1,1)(3,0,0)` | `p0(W_(w^w))` | 数値 | Ytosk |
| 34 | | `Z (2,1,1)(3,1,0)` | `p0(W_W)` | 数値 | Ytosk |
| 35 | | `Z (2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)` | `p0(W_(W_W))` | 数値 | Ytosk |
| 36 | SRO | `Z (2,1,1)(3,1,0)(2,0,0)` | `p0(pI0(0))` | 数値 | なし |

BHO は Bachmann–Howard 順序数、`phi(1,W+1)` は $`\varepsilon_{\Omega_1+1}`$。

この表で確かめたこと：

- 36 個の項 $`J`$ はどれも標準形で、狭義に増える。Python でも Lean でも
- 67 個の証明書をすべて見つけ、再生した：隣り合う 35 組すべてで、$`i`$ 行目の $`\Phi_3`$ は $`i+1`$ 行目の $`\Phi_3`$ より下。
  $`V`$ から後の 31 行で $`\Phi_3(M[2]) \lt \Phi_3(M)`$（$`M[n]`$ は基本列の $`n`$ 番目）。
  $`\Phi_3(\mathrm{SRO}[1]) \lt \Phi_3(\mathrm{SRO}[2])`$
- tr3 は名前を付ける 25 行で、Ytosk は 30 行で同じ $`J`$ を与える。食い違う読み方は無い

**2026-10 の確認**（どの実行も 60 秒以内。証明書は再生したものだけを数える）。

- **STEP の写像 $`B`$。** Weiermann–Wilken 2011 の系と一緒に、InaccPsi の Python 版の横に実装した。ランダムな 7 組の標本
  （それぞれ 12,720 組まで、段は 5 まで）で、$`B`$ の順序の誤りは 0、像はどれも標準形、段 0 の像はどれも
  $`\psi_{\Omega_1}(A + \theta)`$ より下。わざと壊した $`B`$ 2 つは同じ試験で落ちる（順序の誤り 68、標準形でないもの 44）。
  査読者の網羅的な試験（小さな項すべて）：STEP-0 では 3,554 項、630 万組まで、問題 0。$`A = \Omega_\omega + \theta`$ では
  ごく小さな集合（61 項と 35 項）だけで、問題 0。
- **補題 FOLD。** $`\varepsilon_0`$ より下の $`R_1^+`$ のランダムな 9,000 例のすべてで、被覆と恒等写像の最小は被覆だった。
  対照（最大）は 20 回落ちた。先頭の項への置き換えは、ランダムな 9,522 例のすべてで、与えた写像より下の閉じた埋め込みで、
  $`\le_1`$ を前向きに保った。
- **MU-A の写像 $`\mu`$。** 作った $`G_A`$ の 3,913 項のすべてで標準形。査読者が定義だけから書き直したものは、ランダムな
  $`G_A`$ の項（995 列まで）の 47,990 組で順序の誤り 0。表の 36 行のうち 19 行が $`G_A`$ に入り、$`\mu`$ はその行列を与える。
- **下界に向けた証明書**（見つかった 2,511 個をすべて再生した）：

  | 集合 | 証明書あり | 未決 |
  |---|---|---|
  | SRO 未満、7 列以下、読みが項になる根 1 つの標準形の行列 1,423 個。隣り合う組 | 1,422 組中 1,389 | 33 |
  | 10 列以下の $`G_A`$ の項。隣り合う組 | 496 組中 478 | 18 |
  | 329 個の極限での基本列の段 | 658 組中 648 | 10 |
  | 逆順の隣り合う組（対照） | 24 組中 0 | — |

  未決の組で反証されたものは無い。$`\Phi_3`$ の既知の順序の破れ 26 個（58 組）は、どれも SRO より上。
- **DOM₂。** 予想どおりの順序「長さ 3 の鎖の無いパターンは $`m_3`$ より下」の証明書が 4 つの形で見つかり、逆向き 3 つは
  それぞれ 40 秒以内に見つからなかった。$`\Phi_3(M)`$ の最長の鎖：$`(0,0,0)(1,1,1)(2,2,2)(3,3,3)`$ からの 3,875 個の行列
  （行 $`\le 3`$、列 $`\le 24`$）で 2。

**最初の到達不能基数。** 大きさ 9 以下の標準形 1,650,729 個をすべて並べた：$`I`$ の記号を含む最小の可算な項は
$`\psi_{\Omega_1}(\psi_{I_0}(0))`$ で、$`I`$ の記号を含まない可算な項はすべてそれより下（確認済み。いまはすべての項について補題 I-FREE で証明済み）。予想：$`I_0`$ が
要る最初のパターンは $`\Phi_3(\mathrm{SRO})`$（$`\mathrm{SRO} = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)`$）で、その点は
$`\psi_{\Omega_1}(\psi_{I_0}(0))`$。根拠：$`\mathrm{SRO}[n]`$ は高さ $`n+2`$ の $`\Omega`$ の塔の $`\psi_{\Omega_1}`$ と読める。
証明書で $`n = 2, 3`$ の $`\Phi_3(\mathrm{SRO}[n]) \lt \Phi_3(\mathrm{SRO})`$。$`n = 4`$ は時間切れ。$`I_1`$ が最初に要る場所は
未解決。

**鎖と $`\Phi_3`$。** $`V_3`$ から $`(0,0,0)(1,1,1)(2,2,2)(3,3,0)`$ までの 14 個の行列で、パターン $`\Phi_3(M)`$ の
$`\le_2`$ 鎖の長さは 2 以下（確認済み。上の 3,875 個でも）。DOM₂（証明済み）により、そういうパターンの点はどれも
$`m_3 \lt \min C^*_3`$ より下。以前の 8 個の証明書は、もう要らない。予想 CH が正しければ、順序を保つ $`\Phi_3`$ は、最初の
到達不能基数を越えたら長さ 3 以上の鎖を使わなければならない。長さ 2 の鎖だけでは $`\psi_{\Omega_1}(I_\omega)`$ に届かない。
この帰結は**証明されていない**：「$`\Phi_3`$ は長さ 3 の鎖を作らない」は確認済みだけで、しかも $`R_2^C`$ だけの話である。

## 7. ファイル

| ファイル | 何を証明するか |
|---|---|
| [CountSeg.lean](CountSeg.lean) | 補題 L、`bounded_inter_Om1`、`vals_inter_Om1`、`three_bounds` |
| [LowSeg.lean](LowSeg.lean) | 補題 IS と補題 CONT |
| [ConjT.lean](ConjT.lean) | 定理 T-UP の InaccPsi 側：$`A_\eta`$ での (HA)、STEP を仮定とした $`\eta = \omega^2`$ までの帰納法、そこからの予想 U、補題 M の算術 |
| [LowTerms.lean](LowTerms.lean) | §4 の 7 つの項 $`u(\eta)`$：標準形、値、順序、$`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ |

$`R_2^+`$ そのものについては、Lean には何も無い。

## 8. 文献

- T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001).
- T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009).
- G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
- G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
- A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined θ-functions", MLQ 57 (2011).
- G. Wilken, "A glimpse of Σ₃-elementarity" (2020).
- G. Wilken, "Pure Σ₂-elementarity beyond the core", APAL 172 (2021).
- W. Buchholz, "A simplified version of local predicativity" (1992).
- W. Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof Theory (1998), Ch. IV.
