[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/PoR/InaccPsi: $`R_2^+`$ の核についての Wilken の主張

パターン → [InaccPsi](../../../Notation/InaccPsi/README-ja.md)（$`\omega`$ 個の弱到達不能基数の上の
Buchholz の $`\psi`$）の項。このディレクトリには、G. Wilken の主張についての作業を置く。主張が何を言うか、
何が証明済みか、何が未解決か、そして実験。

状態の言葉：**Lean**（Lean で検査済み。`sorry` なし。公理は `propext`、`Classical.choice`、`Quot.sound`
だけ）。**証明済み**（紙の上。独立した査読者が、致命的な点も止める点も無く証明済みと判定。「(2026-10、査読 2 回)」は、2026 年 10 月の結果で、独立した査読者 2 人が確かめたという意味。
回数の書いていない証明済みの結果は査読 1 回）。**引用**
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

どちらの半分も**未解決**。$`\upsilon_{\omega\cdot\omega}`$ より下では両方とも成り立ち、$`R_2^C`$ では
$`\Phi_1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Omega_1\cdot 2})`$（$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$）まで成り立つ。$`\Phi_1`$ は
$`\alpha \mapsto \Xi_\alpha`$ の最初の不動点で、$`\Xi_\alpha`$ は $`\iota \mapsto \upsilon_\iota`$ の $`\alpha`$ 番目の不動点（§3、[RESTARTS-ja.md](RESTARTS-ja.md)、
[REACHES-ja.md](REACHES-ja.md)）。今は $`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$ まで成り立つ
（[PINS-ja.md](PINS-ja.md) §3）。核の側だけなら $`R_2^C`$ でさらに先、$`[0, \nu_C]`$ で証明済み。$`\nu_C \gt \nu_P`$ は $`R_2^C`$ が骨組み型でなくなる最初の点
（[BREAK-ja.md](BREAK-ja.md) §2）。

## 3. 証明済みのこと

**まとめ。** $`\upsilon_{\omega\cdot\omega}`$ より下では、主張は $`R_2^C`$ でも $`R_2^S`$ でも成り立つ：$`\upsilon_{\omega\cdot\omega}`$ 未満の
どの順序数も核に入り、しかも、つぶす引数がすべて $`I_\omega`$ 未満の InaccPsi の標準形の可算な値である（下の定理 LOW）。
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
評価は証明されておらず、そのような評価は、ちょうど $`\nu_C`$ より上の 1 点での 3 つの関係。$`C^*_3`$ は $`\omega_1^{CK}`$ より下（Carlson 2009,
Thm 15.2）だが、InaccPsi の項による上からの評価も名前もまだ無い。$`R_2^C`$ では $`\Lambda_\varepsilon`$ より上（核の側は $`\nu_C`$ まで証明済み）、$`R_2^S`$ では
$`\upsilon_{\omega^3}`$ より上で、どちらの半分も未解決。

**Lean**（このディレクトリの 5 つのファイル。ライブラリ全体と一緒にビルドした）：

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
- **定理 T-LOW の InaccPsi 側**（`LowerT.lean`）。$`\psi_{\Omega_1}(\Omega_\omega) \le u(1)`$ と LOW-STEP の段（$`A = A_\eta`$ の場合だけ
  仮定する）を満たすどの単調な $`u`$ でも、$`\eta \le \omega^2`$ で $`\psi_{\Omega_1}(A_\eta) \le u(1+\eta)`$（`lower_bound`、
  `lower_bound_ww`）。`upper_bound` の仮定も合わせると $`u(1+\eta) = \psi_{\Omega_1}(A_\eta)`$（`conjT`、`conjT_ww`）。LOW-0 と
  LOW-STEP は仮定で、写像 $`E`$ は Lean に無い。

**紙の上で証明し、査読済み。** どの査読も反論を試みるものだった。ここに挙げる結果に対して、致命的な点や止める点を
見つけた査読は無い（止める点のある主張が 1 つあり、「証明されていない」と書いて載せる）。ほかの止める点は未解決の目標についてのもので、「証明されていないこと」に書く。

**$`\upsilon_{\omega\cdot\omega}`$ より下。**

- **定理 CORE-C。** $`\upsilon_{\omega\cdot\omega}`$ 未満の順序数はどれも $`\mathrm{Core}(R_2^C)`$ に入る。証明：定理 EQB の
  上限により、$`\alpha \lt \upsilon_{\omega\cdot\omega}`$ はどれも、上のすべてに $`\le_1`$ ではない。Carlson 2009,
  Thm 14.14 により、核はそういう最小の順序数（または Ord 全体）。
- **補題 RESTR。** $`\Omega_\omega`$ より下では、InaccPsi の包と、到達不能基数 1 個の Pohlers の系（Pohlers,
  "Subsystems of set theory and second order number theory", Handbook of Proof Theory 1998,
  Def 3.4.4.1）の包は一致し、$`\psi_{\Omega_{n+1}}`$ も一致する。引用した $`\mathrm{ID}_{\lt\omega}`$ の順序数
  （Wilken 2021, §1。Pohlers 1998, Fig. 1）と合わせて $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$
  （引用、間接）。文献の中に弱い所が 2 つある：Pohlers は再帰的正則順序数を正則基数に置き換えることを証明なしに
  行う。Wilken は $`\mathrm{ID}_{\lt\omega}`$ の順序数を証明なしに述べる。いまは下の定理 STEP-0 と LOW-0 で
  $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ が直接出るので、この引用はもう要らない。
- $`\psi_{\Omega_1}(0) = \Gamma_0`$、$`\vartheta_0(\varepsilon_{\Omega+1}) = \psi_{\Omega_1}(\varepsilon_{\Omega_1+1})`$（引用 + RESTR）。
- **定理 MAIN。** 次は同値：(i) $`\upsilon_{\omega\cdot\omega}`$ 未満の $`\mathrm{Core}(R_2^C)`$ の順序数はどれも可算な
  InaccPsi の項の値。(ii) $`\upsilon_{\omega\cdot\omega}`$ 未満の順序数はどれもそう。(iii) **予想 U**：
  $`\upsilon_{\omega\cdot\omega} \le D`$。ここで $`D = \sup_a \psi_{\Omega_1}(a)`$。証明：CORE-C と補題 IS。
- **定理 STEP**（2026-10、査読 2 回）。Wilken の点：$`\upsilon_0 = 0`$、$`\upsilon_{\xi+1} = T^{\upsilon_\xi} \cap \Omega_1`$、極限では上限
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
  証明を支える新しい補題は SAME-SET、N、N2、M。2 回目の査読は、写像 $`B`$ を自分のコードでも確かめた（誤り無し）。
- **定理 T-UP**（2026-10、査読 2 回）。どの $`\eta \lt \Gamma_0`$ でも $`\upsilon_{1+\eta} \le \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$。
  証明：STEP で帰納法。極限は補題 CONT。$`\eta = \omega^2`$ までの帰納法は Lean にある（`ConjT.lean`）。
- **予想 U は証明された**（2026-10、査読 2 回）：$`\upsilon_{\omega\cdot\omega} \le \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+2}) \lt D`$。MAIN により、
  $`\upsilon_{\omega\cdot\omega}`$ 未満のどの順序数も可算な InaccPsi の標準形の値で、つぶす引数は
  $`\Omega_\omega + \omega^{\theta+2} \lt I_\omega`$ 未満（補題 L）。
- **定理 LOW-0**（2026-10、査読 1 回）。$`\psi_{\Omega_1}(\Omega_\omega) \le \upsilon_1`$。STEP-0 と合わせて
  $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$。2 つの包を直接比べて示す。
- **定理 LOW-STEP**（2026-10、査読 1 回）。$`\sigma`$ を $`\varepsilon`$ 数、$`A = A_\eta`$、$`\psi_{\Omega_1}(A) \le \sigma`$ とする。すると
  $`\psi_{\Omega_1}(A + \theta) \le \bar T^\sigma \cap \Omega_1`$。カントール標準形の最後の項が $`\theta`$ 以上のどの $`A \ge \Omega_\omega`$ でも
  成り立つ。この条件が無いと証明されていない（例：$`A = \Omega_\omega + 1`$）。証明の筋：$`\psi_{\Omega_1}(A+\theta)`$ 未満の
  InaccPsi の標準形から $`\bar T^\sigma \cap \Omega_1`$ への写像 $`E`$（$`B`$ と逆向き）。段 $`k`$ の $`\varphi(x, y)`$ は
  $`\bar\vartheta_k(\Omega_{k+1}\cdot\omega^{E x} + E y)`$ へ。$`\psi_{\Omega_{k+1}}(a)`$ は $`\bar\vartheta_k(\Omega_{k+1}^2 + F(E a))`$ へ。ここで
  $`F(x) = \Omega_{m+1}^3\cdot\omega^x`$、$`m`$ は $`x`$ の段（$`F`$ は符号を内側のどの符号よりも上に持ち上げる。定義域の規則が
  それを要る）。$`\psi_{\Omega_1}(A + \zeta)`$ は $`\bar\vartheta_0(G(\mathrm{pmax}\,\zeta) + E\zeta)`$ へ。$`\mathrm{pmax}\,\zeta`$ は $`\zeta`$ の
  いちばん外側にある最大の $`\psi_{\Omega_2}`$ の項で、$`G`$ はそれを同じように持ち上げる。$`\sigma`$ 未満のパラメータは
  そのまま。補題 D：どの像も定義域に入る（Weiermann–Wilken 2011, Lemma 4.3）。補題 M：$`E`$ は狭義に増加（そこの
  Lemma 4.4）。証明を支える新しい補題は PARTS、PMAX、Q、Q1、D、M、ARG0、ARG1。
- **定理 T-LOW**（2026-10、査読 1 回）。どの可算な $`\eta`$ でも
  $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) \le \upsilon_{1+\eta}`$。証明：LOW-0 と LOW-STEP で帰納法。極限は補題 CONT。
  T-UP と合わせて**定理 T**（§4）。$`\eta = \omega^2`$ までの帰納法は Lean にある（`LowerT.lean`）。
- **定理 CORE-S**（2026-10）。$`\upsilon_{\omega^3}`$ 未満のどの順序数も $`\mathrm{Core}(R_2^S)`$ に入る（$`\upsilon_{\omega\cdot\omega}`$ から先は
  補題 FRAG を使う。FRAG は証明済みになった。[RESTARTS-ja.md](RESTARTS-ja.md) §1）。$`\upsilon_{\omega\cdot\omega}`$ より下では、$`R_2^S`$ の最小の閉じた集合は、
  ちょうど $`R_2^C`$ の isominimal な集合。要の段は補題 FOLD：$`f`$ が被覆なら、$`f`$ と恒等写像の各点ごとの最小も
  被覆。ただし $`\lt_2`$ の組が入れ子にならないこと。補題 NEST：長さ 3 の鎖より上では、この条件は成り立たない。
  ここで $`R_2^S`$ での「最小」は Wilken の定義（2021, 6 ページ。+ の無い $`R_2`$ のもの）を $`R_2^+`$ に読んだもの。
- **定理 LOW**（上のまとめ）は、CORE-C、CORE-S、予想 U、補題 L から出る。

**$`\upsilon_{\omega^3}`$ まで、FRAG なしで**（2026-10、$`R_2^C`$）。定理 CORE-C$`^\Xi`$ で $`[0, \Xi_\omega]`$ まで延びた
（[RESTARTS-ja.md](RESTARTS-ja.md) §3）。さらに $`[0, \Lambda_\varepsilon)`$ と $`[0, \rho_{\Theta_P})`$ まで延びた（[REACHES-ja.md](REACHES-ja.md) §2）。
さらに $`[0, \rho_{\Theta_A+\omega^2})`$ まで（[PINS-ja.md](PINS-ja.md) §2）。さらに $`[0, \rho_{\Theta_{d\omega}})`$ まで、さらに $`\nu_C \gt \nu_P`$ で $`[0, \nu_C]`$ まで（[BREAK-ja.md](BREAK-ja.md) §2、§4）。

- **補題 PT**（査読 1 回）。$`Q`$ を Carlson 2009, Def 5.6 の完全な意味でのパターンとする。$`R_2^C`$ の中の $`Q`$ のどの写しも
  $`Q`$ の点を $`\ge v`$ に置くなら、$`[0, v] \subseteq \mathrm{Core}(R_2^C)`$（Carlson 2009, Lemma 15.11, Thms 14.10, 14.14）。
  要るのは 1 つのパターンの下界だけで、順序の命題は要らない。
- **定理 CORE-C3**（査読 1 回）。$`\upsilon_{\omega^3} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+3})`$ 以下のどの順序数も
  $`\mathrm{Core}(R_2^C)`$ に入る。以前は FRAG を仮定したときだけ分かっていた。証明：
  [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の定理 EQB′′ の上限は、ブロックごとに見て FRAG を使わない。それらは、
  $`\alpha \lt \upsilon_{\omega^3}`$ がどれも上のすべてに $`\le_1`$ ではないことを示す。あとは Carlson 2009, Thm 14.14。上限の
  1 つの段（$`\Pi_2`$ 文を移す段で、その式に 2 つの古いパラメータの間の $`\le_1`$ の事実も入っていた）が不完全だった。
  直し方の補題 DIAG′（その事実を式から外す。もう成り立っているから）は証明済み。端の点：$`\Phi_3(V_3)`$ のどの写しも
  点を $`\ge \upsilon_{\omega^3}`$ に置く（上限と補題 TOP から。査読者がこの短い証明を出した）。あとは補題 PT。名前は
  $`\eta = \omega^3`$ での定理 T。補題 IS と合わせると、$`\upsilon_{\omega^3}`$ より下では、$`R_2^C`$ の核も項の可算な値も、
  どちらも $`[0, \upsilon_{\omega^3})`$ 全体。査読の小さな点：Wilken 2007（APAL 145, 162–175）の Claim 5.5(b) の
  $`\tau`$ の選び方が、まだ書かれていない。補題 PT は $`Q`$ がパターンであることが要る（使うパターンでは確認済み）。
- **系**（査読 1 回）。FRAG なしで $`m_3 \ge \upsilon_{\omega^3}`$、$`\min C^*_3 \ge \upsilon_{\omega^3}`$（$`m_3`$ の定義は下の「鎖」）。

**$`R_2^S`$ と $`R_2^C`$**（2026-10）。2 つの構造で、ある関係 $`\alpha \le_i \beta`$ が食い違う最小の段 $`\beta`$ を
$`\beta_0`$ とする（等しければ $`\beta_0 = \infty`$）。$`\beta \ge \kappa`$ のすべてで $`\kappa \le_1^X \beta`$ となる最小の $`\kappa`$ を $`\kappa_X`$ とする。

- **補題 STAGE。** $`\beta`$ より下のすべての組で 2 つの構造が一致するなら、$`\alpha \le_1^S \beta \Rightarrow \alpha \le_1^C \beta`$。
  さらに $`\beta`$ への $`\le_1`$ も一致するなら、$`\alpha \le_2^S \beta \Rightarrow \alpha \le_2^C \beta`$。道具：有限集合による判定
  （下の T1）、定理 EQ の先頭の項への置き換え、Wilken 2021 の Lemma 1.7(2) の $`R_2^+`$ 版、$`\Pi_2`$ 文の移し。
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
  最初の部分で成り立つ（概略だけ、[FANFREE-ja.md](FANFREE-ja.md) §3）。今は、臨界な添字の最初の極限より下の、より大きい部分で証明済み（[FANFREE-ja.md](FANFREE-ja.md) §7.3）。
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
  - **R-OM。** (R)「$`\gamma \ge \kappa_C`$ のどれでも $`\kappa_C \le_1^S \gamma`$」は $`\kappa_C \le_1^S \Omega_1`$ と同値（HULL からの
    $`\kappa_C \le \Omega_1`$ を使う）。(E) の下では、$`\gamma \in [\kappa_C, \beta_0]`$ のどれでも成り立つ。
  - **AGR は (E) かつ (R) と同値。** AGR に W(C) は要らない。要るのは「$`= \rho`$」のときだけ。
  - 未解決：**PIN**（拡張を上向きの写しから $`Y^\circ`$ そのものへ戻す）と **LOW**（新しい点が $`\max X`$ 以下にある拡張、
    または新しい点の最小が加法的主要数でない拡張）。示されているのは「PIN と LOW から CORE-2」の向きだけ。

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
  FRAG なしで $`m_3 \gt \Xi_\omega`$、$`c_0 \ge \upsilon_{\Xi_\omega+\omega^2}`$（[RESTARTS-ja.md](RESTARTS-ja.md) §3）。いまは
  $`m_3 \ge \Lambda_\varepsilon \gt \Phi_1`$（[REACHES-ja.md](REACHES-ja.md) §5）。再生した証明書から、$`m_3`$ は
  $`\Phi_3((0,0,0)(1,1,1)(2,2,2)(3,3,3))`$ の点より上。$`m_3`$ は $`\upsilon`$ の点で、
  $`c_0`$ は $`\iota \mapsto \upsilon_\iota`$ の不動点の集まりのはしごの $`\omega^\omega`$ 段目にある（定理 C3-VEB、[PINS-ja.md](PINS-ja.md) §4。
  その仮定 INC1 は今は証明済み、[BREAK-ja.md](BREAK-ja.md) §1）。$`m_3`$ とどの扇の頂点も、骨組み型でない最初の点（$`R_2^S`$ では $`\nu`$、補題 CAP。
  $`R_2^C`$ では $`\nu_C`$、定理 NU-CT）より上で、その点は $`\gt \nu_P`$。$`R_2^S`$ での $`m_3 \gt \nu_P`$ は査読 2 回（[BREAK-ja.md](BREAK-ja.md) §2–3）。
  どの深さの入れ子の組も、最小の上端は $`m_3`$ より下（NEST、査読 2 回、[BREAK-ja.md](BREAK-ja.md) §5）。どの扇の頂点も、その極限
  $`T_\omega`$ より上で、仮定は要らない（査読 2 回）。最小の扇の $`\lt_2`$ の後の元はちょうど 2 つで、2 つ目はその届く先。$`R_2^C`$ では
  最小の扇は開いているので、最小の閉じた扇より真に下。仮定 $`FF_N`$（未解決）のもとでは、最初の扇、$`m_3`$、$`C^*_3`$ に到達不能基数が
  要る（[BREAK-ja.md](BREAK-ja.md) §7.4）。$`R_2^C`$ では（[COVER-ja.md](COVER-ja.md)、どれも査読 1 回）：核の点が長さ 3 の鎖の底であるのは、
  右端の無限の $`\le_1`$ 鎖を持つときちょうど（定理 CP3）。$`c_0`$ はそういう最小の点で、$`c_1`$ は下向きの 2 反映が作る $`\omega`$ 列の上限
  （LEAST3）。最小の閉じた $`n`$ 扇（頂点 $`\varphi_n`$）は $`m_3`$ より下にとどまるので $`c_0 \gt m_3 \ge \sup_n \varphi_n \gt f_0 \gt x_F`$（FIN-FAN）。$`FF_{cl}`$
  （$`\sup_n \varphi_n \ge \theta_0`$）を仮定すれば $`C^*_3`$ に到達不能基数が要る。最初の扇に要るための十分条件は、$`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)) の点
  （それは $`\min\{m : m \le_1 x_F\}`$）が $`\ge \theta_0`$ という 1 つの命題（逆は未解決）。今は（どれも査読 1 回、[COVER-ja.md](COVER-ja.md) §5.2〜5.3）：最小の扇の
  順序型は $`\omega^2`$。その命題は、右端に届く先の無い、扇の無いパターンについての下からの評価と同じで、$`\theta_0`$ より下の下界の
  計画から出る。そして $`c_2 \lt \omega_1^{CK}`$。さらに（どれも査読 1 回、[COVER-ja.md](COVER-ja.md) §6）：$`m_F \gt \nu_C`$。パターンの間の比較の計算で、
  $`\theta_0`$ のいちばん上の段といくつかの一様な段の族を証明した。名前 $`m_F = \psi_{\Omega_1}(B_F)`$ について $`B_F \ge \psi_{I_0}(0)`$ ⇔ $`m_F \ge \theta_0`$。$`B_F = I_0`$
  での名前は予想。さらに（どれも査読 1 回、[FANFREE-ja.md](FANFREE-ja.md) §4）：$`m_F`$ は組の列 $`\mathrm{CH}_k`$ の点の極限で、$`\sigma_N = m_F`$。
  さらに（どれも査読 1 回、[FANFREE-ja.md](FANFREE-ja.md) §7.2 と §7.4）：配置 L1p の無い扇の無いパターンはどれも $`\iota(\mathrm{CH}_2)`$ より下にあり、
  $`\iota(\mathrm{CH}_2) \lt t`$ は、$`t`$ より下のある 1 点 $`a`$ が $`a \lt_2 b`$、$`b \lt c`$ となる組 $`c \lt_2 d`$、$`a \le_1 d`$ を持つことと同値。
  以前から：$`C^*_2 = \{\upsilon_\omega, \upsilon_{\omega+1}\}`$。
- **補題 TOP2**（2026-10、査読 1 回）。どの $`\alpha \lt m_3`$ にも、$`\alpha \lt x \lt y \lt m_3`$ となる長さ 2 の鎖 $`x \lt_2 y`$ がある。
  だから $`m_3`$ は長さ 2 の鎖の極限で、FRAG なしで $`m_3 \ge \upsilon_{\omega\cdot\omega}`$。
- **補題 REL**（2026-10、査読 1 回。出発点を変えた定理 STEP）。$`r_0 = \tau`$、$`r_{\xi+1} = T^{r_\xi} \cap \Omega_1`$、極限では上限とする。
  $`\tau`$ が $`\varepsilon`$ 数で、$`\tau \le \psi_{\Omega_1}(A)`$、$`\Omega_\omega \le A`$、$`A + \theta\cdot\zeta`$（$`\zeta \lt \Gamma_0`$）が (HA) を満たすなら、
  $`\eta \lt \Gamma_0`$ で $`r_{1+\eta} \le \psi_{\Omega_1}(A + \theta\cdot(1+\eta))`$。だから $`\psi_{\Omega_1}(A)`$ より上でやり直すと、1 段の
  費用は $`+\Omega_\omega`$ ではなく $`+\theta`$。
- 小さな補題：**PRINC**（$`x \lt_1 y`$ なら $`x`$ は加法的主要数。$`x \lt_2 y`$ なら $`y`$ は加法的主要数）、
  **ISO-UNION**（isominimal な集合の有限個の合併は isominimal）、**HULL**（非可算な正則基数 $`\kappa`$ は、上の
  すべてに $`\le_1`$。両方の構造で）、**DOM₁**（$`\lt_2`$ の組を持たないパターンの最小の実現は $`\upsilon_1`$ より下）。
- **$`\Phi_3`$ が作る鎖**（2026-10、査読 1 回）。**定理 A**：どの入力の行列でも（標準形でなくても）、$`\Phi_3`$ が出力する
  $`\le_2`$ の関係には $`x \lt_2 y \lt_2 z`$ が無い：組の右端は決して左端にならない。だから鎖の長さは 2 以下。**定理 B**（片向き）：
  この関係を、推移性と Carlson の規則「$`a \le_2 b`$ かつ $`a \le_1 x \le_1 b`$ なら $`a \le_2 x`$」で閉じる。BAR_R を次のように書く：
  $`a`$ の右端が $`d_1 \lt \dots \lt d_q`$ で、左端になりうる点 $`y`$ が $`d_{k-1}`$ と $`d_k`$ の間にあれば（$`d_0 = a`$）、$`y \le_1 d_k`$ ではない。
  BAR_R なら、閉じた関係に長さ 3 の鎖は無い（逆向きは証明されていない）。**系 C**：$`\Phi_3(M)`$ がパターン（Carlson 2009,
  Def 5.6）なら長さ 3 の鎖は無く、DOM₂ によりその点は $`m_3`$ より下（$`R_2^C`$ で）。**補題 LAM**：2 つの組の範囲は、入れ子か
  離れているかで、交差しない。入れ子は実際に起こる。reach の性質 CONE から BAR_R が出る。未解決：BAR_R と CONE。BAR_R は
  標準形でない入力で破れることがあるので、証明には標準形であることを使う必要がある。
- **長さ 3 の鎖を具体的に求めて**（2026-10、査読 1 回）。予想 C3′ の上半分についての結果：
  - **集合論の反映。** ELEM：$`H`$ がある $`H(\vartheta)`$ の初等部分モデルで $`H \cap \gamma = \delta`$ が順序数なら、$`R_2|\delta`$ は $`R_2|\gamma`$ の
    初等部分構造（$`R_2^S`$ でも $`R_2^C`$ でも）。CLUB-1：非可算な正則 $`\kappa`$ では、$`\delta \le_1 \infty`$ となる $`\delta \lt \kappa`$ は club を含む。
    CHAINS-S：$`R_2^S`$ ではそのうちのどの 2 つも $`\le_2`$ なので、$`R_2^S`$ には可算な順序数の中にどの有限の長さの鎖もある。
    HIGH：そういう $`\delta`$ はどれも $`\omega_1^{CK} \gt \psi_{\Omega_1}(\Lambda)`$ より上なので、この方法では InaccPsi の範囲の中に鎖は出ない。
  - **基数での $`\le_2`$。** LOCAL-2：HULL の写しは、$`\pi(\beta)`$ より下のすべての拡張で T2 の拡張の条件を満たす（$`Y \subseteq H`$ が
    要る）。破れうるのは $`[\pi(\beta), \kappa)`$ の点を通してだけ。CHANG-2（条件つき）：Chang 型の包の仮定から $`R_2^S`$ で
    $`\kappa \le_2 \lambda`$。その仮定は $`\lambda \ge \kappa^+`$ を強いる。SC2：$`V_\kappa \prec_{\Sigma_2} V_\beta`$ なら $`R_2^S`$ で $`\kappa \le_2 \beta`$。
    I0-NOT-SIGMA2：$`I_0`$ が最小の弱到達不能基数なら、$`V_{I_0}`$ は $`\beta \ge I_0 + 2`$ のどの $`V_\beta`$ でも $`\Sigma_2`$ 初等ではない。
    REFORM：「$`I_0 \le_2 \lambda`$」は $`\omega_1^{CK}`$ より上の 2 つの順序数についての命題と同値。未解決：ある $`\beta \gt I_0`$ で
    $`I_0 \le_2 \beta`$ か。
  - **NO-PROMOTE。** $`\tau = \upsilon_{\omega^2}`$ は $`\tau \le_1 \upsilon_{\omega^2+\omega+1}`$（$`\tau`$ の上のやり直し $`r_{\omega+1}`$）となる
    $`\varepsilon`$ 数だが、$`\{\upsilon_{\omega^2+1}, \upsilon_{\omega^2+\omega}, \upsilon_{\omega^2+\omega+1}\}`$ は鎖ではない（R2PLUS の補題 TOP と
    定理 B′′。$`R_2^S`$ では FRAG なし、$`R_2^C`$ では EQB′′ を通す）。だから $`\tau`$ の $`\le_1`$ の届く先だけでは C3′ は示せない。
    $`c_0`$ の $`\le_2`$ の性質が要る。
  - **補題 K と COLLAPSE-FAIL。** 包 $`\mathrm{Cl}(0, 0) \cap \Omega_2`$ のつぶしは、置き換え $`\Omega_1 \mapsto \Gamma_0`$（証明済み）。
    $`\Omega_1 \le_1 \varepsilon_{\Omega_1+1}\cdot 2`$（証明済み）。「$`\Gamma_0 \le_1 \varepsilon_{\Gamma_0+1}\cdot 2`$ ではない」は**証明されていない**：
    査読が止める点を見つけた（証明が右端そのものを $`Y`$ の点に使うが、判定 T1 はそれを許さない）。査読者は直し方を
    出したが、それはまだ査読されていない。これが成り立てば、InaccPsi の包をつぶしても $`\le_1`$ は保たれず、基数での
    $`\le_2`$ の関係を可算な値へ下ろすことはできない。

**下界に向けて**（2026-10、$`R_2^C`$）。$`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$ と書く。

- **補題 I-FREE。** 可算な標準形が到達不能基数の記号を含まないことと、その値が $`\theta_0`$ 未満であることは同値。
  だから到達不能基数を使わない項は、ちょうど $`\theta_0 \lt \psi_{\Omega_1}(I_0)`$ 未満の項。
- **補題 OE。** $`\gamma`$ 未満の標準形から点つきパターンへの写像 $`F`$ で、「$`F(t)`$ の最小の実現の点」が $`t`$ について
  狭義に増加するものがあれば、$`[0, \gamma) \subseteq \mathrm{Core}(R_2^C)`$。**EPS-RED**：$`F`$ は値が $`\varepsilon`$ 数の項でだけ
  要る。**FS-OE**：狭義の増加は 2 つの局所的な段「前の項は $`t`$ より下」「$`t[n]`$ は $`t`$ より下」から出る。
- **RED-BMS。** [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の定理 S と合わせると、$`\gamma`$ より下の下界は、
  $`\gamma`$ 未満の $`\varepsilon`$ 数の項から $`V`$ 未満（FRAG を使えば $`V_3`$ 未満。FRAG は証明済み）の標準形のトリオ行列への順序を保つ
  埋め込み $`\mu`$ から出る。**S-RED**：Lean のクラス `TrioStdL` の行列では、$`\Phi_3`$ の点の狭義の増加は、ただ 1 つの命題
  「どの $`A`$ と $`k`$ でも $`\Phi_3(A[k])`$ の点は $`\Phi_3(A)`$ の点より下」に帰着する（Lean の定理 `trio_fs` と BMS の停止性から）。
- **補題 MU-A。** 項の断片 $`G_A`$（和。$`\Omega_\omega`$、$`\omega^{\Omega_\omega + c}`$、$`\theta\cdot\omega^e`$ の和の $`\psi_{\Omega_1}`$）の上で、
  トリオ行列への再帰的な写像 $`\mu`$ は狭義に増加。
- **補題 UNIF-V。** $`A_m = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)^m`$（$`m \ge 3`$）とどの $`N`$ でも、$`\Phi_3(A_m[N])`$ の点は
  $`\Phi_3(A_m)`$ の点より下。$`\Phi_3`$ の出力の形を仮定する（$`m \le 8`$、$`N \le 6`$ で確認済み）。R2PLUS の定理 V
  （$`m = 2`$）を広げる。$`m = 3`$ では、出力の形がどの $`N`$ でも与えられた（2026-10、査読 1 回）。ただしその補題は
  スケッチしか書かれていないので、$`m = 3`$ は証明済みに数えない。CORE-C3 はこれを使わない。
- **補題 MU-B**（2026-10、査読 1 回）。もっと大きな断片 $`G_B \supset G_A`$：可算な極限の添字 $`\Omega_\xi`$（$`\xi`$ の中に
  $`\psi_{\Omega_1}`$ の項があってもよい）、可算な $`\kappa \ge 1`$ と $`c`$ での項 $`\omega^{\Omega_\xi\cdot\kappa + c}`$、添字の違う項の和、
  $`\theta`$ の尾、$`x \ge \psi_{\Omega_1}(\Omega_\omega)`$ での可算な $`\omega^x`$。広げた写像 $`\mu_B`$ は、$`G_A`$ の上では $`\mu`$ に等しく、
  $`\psi_{\Omega_1}(\Omega_\xi)`$（$`\xi \lt \varepsilon_0`$ は極限）では Lean の写像 `omegaIndexMatrix` に等しい。$`\mu_B`$ は $`G_B`$ の上で
  狭義に増加し、どの像も SRO より下。像が標準形であること：証明済み（Lean `trioStdL_omegaIndexMatrix`）なのは
  $`\psi_{\Omega_1}(\Omega_\xi)`$（$`\xi \lt \varepsilon_0`$ は極限）だけ。ほかは確認済み。査読は止める点を 1 つ見つけた。MU-B そのもの
  ではなく、MU-B を核に使うことに対して：核の分かっている部分に順序数は増えない。$`G_B`$ には
  $`[\varepsilon_0, \psi_{\Omega_1}(\Omega_\omega))`$ の元が無く（証明済み）、順序型は小さい（予想：アッカーマン順序数くらい）。補題 OE が
  与えるのは $`[0, \mathrm{otp}(G_B))`$ だけ。次の段では、$`\varepsilon_0`$ と $`\psi_{\Omega_1}(\Omega_\omega)`$ の間の $`\varepsilon`$ 数を
  覆わなければならない。
- **補題 MU-0**（2026-10、査読 1 回）。$`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ 未満の標準形は、辞書式順序の標準形のペア数列（空のものを
  含む）と順序同型。写像 $`\mu_0`$ は和を連結に、加法的主要数の項を根が 1 つの数列に送る。引用 1 つを仮定して証明済み：
  $`\upsilon_1`$ は Buchholz の $`\psi_0(\Omega_\omega)`$ に等しい（Lean の公理 `core_eq_psi`。出典は Buchholz 1986 で、最初に引いた
  Wilken 2007 ではない）。Lean の定理（`pairOrd_injective`、`range_pairOrd`、`ordOf_append'`、`lemmaR`）も使う。$`\mu_0`$ は
  「値をとり、ペアの順位の逆をとる」もので、項の上の再帰ではない。
- **補題 MU-B0**（2026-10、査読 1 回）。MU-B は $`G_{B0}`$ の上でも成り立つ。$`G_{B0}`$ は、土台を $`\upsilon_1`$ 未満のすべての加法的主要数の
  項に広げた $`G_B`$ で、土台では $`\mu_0`$ を使う：$`\mu_B`$ は狭義に増加し、どの像も SRO より下。像が標準形であることは
  確認済みだけ。**すき間**（証明済み）：$`G_{B0}`$ は $`[0, \varepsilon_{\upsilon_1+1})`$ を含み、そこから $`\upsilon_2 = \psi_{\Omega_1}(\Omega_\omega + \theta)`$
  までは何も含まない。だから段 0 の族 (M4) は、そこで核の証明済みの部分に順序数を足さない（まったく足さないことは
  もっともらしいが、証明されていない）。次のすき間は 1 つ上の段の土台（引数 $`\Omega_\omega + \zeta`$、$`\zeta \lt \theta`$。補題 TR1、未解決）。

**証明されていないこと：**

- **$`R_2^C`$ で $`\Lambda_\varepsilon`$ より上、$`R_2^S`$ で $`\upsilon_{\omega^3}`$ より上での主張**、両方の半分。$`\Theta_A`$ より上の
  やり直しの届く先（$`\Theta_A`$ そのものでの届く先は今は分かっている）と、[FANFREE-ja.md](FANFREE-ja.md) §10、[COVER-ja.md](COVER-ja.md) §9、[BREAK-ja.md](BREAK-ja.md) §10、[PINS-ja.md](PINS-ja.md) §6、[REACHES-ja.md](REACHES-ja.md) §7、[RESTARTS-ja.md](RESTARTS-ja.md) §6 の残り。
- **$`R_2^S = R_2^C`$**：$`\le_1`$ の逆向き $`C \Rightarrow S`$ は、$`\kappa_C`$ より上の後続の段で $`\alpha \notin G_C`$ のとき未解決。
  $`\le_2`$ の逆向きは、(ii) の型の段で未解決（$`\Pi_2`$ 文を上向きに移すことが要るが、上向きの 2-反映でも持ち上げでも
  得られない。いまは段ごとに 1 つの組 $`(a^*, \beta)`$ の話で、$`\kappa_C`$ より下では予想 CORE-2 と同値。残りは PIN と LOW）。
  Σ2-GAP、INC、W(C)、(R)、AGR、$`\beta_0 = \infty`$ も未解決。定理 CC とすべての証明書は $`R_2^C`$ の話。
- **$`\theta_0`$ より下の下界**（査読：この目標に向けた止める穴。本文の誤りではない。$`V_3`$ より上の標本の決まらない 26 個の極限の
  跳びは今は証明済み、[FANFREE-ja.md](FANFREE-ja.md) §1。SRO より下の段は今は標本の 3,166 個のうち 459 個で、すべての $`n`$ で証明済み、
  [FANFREE-ja.md](FANFREE-ja.md) §7.1）：$`\theta_0`$ 未満のすべての
  $`\varepsilon`$ 数の項から SRO 未満の標準形のトリオ行列への順序を保つ埋め込み $`\mu`$ と、SRO 未満のすべての行列での
  S-RED の局所的な段。$`G_B`$ の外に 4 つの族がある：(M1) 項の中の非可算な $`\kappa`$、$`c`$、$`g`$。(M2)
  $`\Omega_{\xi+1}`$ のような後続の添字。(M3) $`\Omega_{\Omega_\omega}`$ のような非可算な添字。(M4) $`\psi_{\Omega_1}(\Omega_\omega)`$ より下の土台
  全体（$`\varepsilon_1`$、$`\Gamma_0`$、$`a \ge 1`$ の $`\varphi(a, b)`$ など）。段 0 の (M4) は済んだ（MU-0、MU-B0）が、核には何も足さない。
  残り：段 1 以上の (M4)（補題 TR1）、(M1)–(M3)、$`V_3`$ より上での局所的な段。Wilken の $`\upsilon`$ の範囲の中では、下界は
  代わりに届く先の上限から出て、いまは $`[0, \rho_{\Theta_P})`$ まで（CORE-C$`^+`$、[REACHES-ja.md](REACHES-ja.md) §2）。その先に区間 $`[\theta_0, \psi_{\Omega_1}(I_0))`$ があり、
  $`\psi_{I_0}`$ でつぶす項が要る。
- **$`C^*_3`$ を具体的に。** 予想 C3′（+ の無い $`R_2`$ での Wilken の最小の 3 鎖、2021, 19–21 ページ、CH、補題 REL から）。
  $`P = \theta = \psi_{\Omega_2}(\Omega_\omega)`$、$`E = \varepsilon_{I_0+1}`$ として $`m_3 = \psi_{\Omega_1}(E)`$、
  $`C^*_3 = \{\psi_{\Omega_1}(E + P),\ \psi_{\Omega_1}(E + \omega^{P+1}),\ \psi_{\Omega_1}(E + \omega^{P+1} + P)\}`$。
  どれも標準形で、$`\psi_{\Omega_1}(I_0)`$ と $`\psi_{\Omega_1}(I_1)`$ の間にある（Python と Lean で確認済み）。以前の予想は、3 つの鎖の項で
  $`E`$ の代わりに $`E + \Omega_\omega`$ だった。REL により、それはもとの読み方（$`m_3`$ より上でやり直した $`\upsilon`$ の階層）に
  合わない。やり直しの費用は $`+\Omega_\omega`$ ではなく $`+P`$ だから（二者択一として証明、査読 1 回）。いまはその読み方
  そのものが否定された：ある点の上でやり直した 3 点は決して鎖にならない（C3′-FALSE、査読 1 回、[REACHES-ja.md](REACHES-ja.md) §5。補題 LEFT を使うが、それは今は
  証明済み、[BREAK-ja.md](BREAK-ja.md) §1）。
  だから数の形の C3′ には導き方が残っていない。直した形 C3′′ も偽：$`c_0, c_1, c_2`$ はどれも集まり
  $`C_{\omega^\omega}`$ の極限点（定理 C3′′-FALSE、[BREAK-ja.md](BREAK-ja.md) §3）。長さ 3 の鎖とはちょうど、後の元を無限に持ち、その極限が
  左端である扇（定理 CF、条件なし）。$`R_2^C`$ では、これは今は 1 つの点の右端の間の $`\le_1`$ の条件（定理 CP3、[COVER-ja.md](COVER-ja.md) §1）。
  これは鎖の特徴づけで、場所は決めない。上半分は未解決：知られている $`R_2^C`$ の $`\le_2`$ の関係
  （$`\Lambda_\varepsilon`$ まで）は長さ 3 の鎖を作らない（定理 BLK$`^O`$）。鎖は Carlson の生成の種の中に無ければならない（NO-GEN）。集合論の反映は $`\omega_1^{CK}`$ より上にしか鎖を
  作らず（HIGH）、$`\le_1`$ の届く先だけでは鎖にならない（NO-PROMOTE）。Carlson 2009, Thm 15.2 から $`c_2 \lt \omega_1^{CK}`$ が出るが、
  InaccPsi の項による評価は証明されていない（[COVER-ja.md](COVER-ja.md) §5.2）。そういう評価には、その下の組 $`a \lt_2 c`$ 1 つと、間にある 2 つ目の
  左端 $`b \lt_2 c`$ があれば足りる（補題 CRIT、[COVER-ja.md](COVER-ja.md) §6.2、査読 1 回）。評価を始まりと 1 段ごとの費用に分けることは、評価
  そのものと同じ。下半分も未解決：長さ 3 の鎖の無いパターンで
  $`\theta_0`$ より下の下界の計画を進めることが要る。
- $`\Phi_3(M)`$ がパターンであること。そうなら長さ 3 の鎖は無く（系 C）、DOM₂ によりその点は $`m_3`$ より下。出力された関係
  そのものにはそういう鎖は無い（定理 A、証明済み）。閉じた関係では BAR_R（確認済みだけ）。

## 4. Wilken の点の名前（定理 T）

**定理 T**（証明済み。上半分 T-UP は査読 2 回、下半分 T-LOW は査読 1 回）。$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$ として、
どの $`\eta \lt \Gamma_0`$ でも、とくに $`\eta \le \omega^2`$ で。さらに定理 T+（査読 2 回、[RESTARTS-ja.md](RESTARTS-ja.md) §4）により、
$`\iota \mapsto \upsilon_\iota`$ の最初の不動点 $`\Xi_1`$ 未満のどの $`\eta`$ でも（その先は、[REACHES-ja.md](REACHES-ja.md) §2 の定理 T++ が
$`\Phi_1`$ までのすべての $`\Xi_\alpha`$ とその間の点に名前を付け、[PINS-ja.md](PINS-ja.md) §3 の定理 GEN が
$`\upsilon^* \le \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ より下の $`\upsilon`$ の点に名前を付ける：標準形を与える $`\eta \lt \Omega_2`$ の集合を $`D`$、
$`D \cap \eta`$ の順序型を $`\iota(\eta)`$ とすると、$`D`$ のどの $`\eta`$ でも $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) = \upsilon_{1+\iota(\eta)}`$。GEN-EXT がこれを
$`\eta \lt \Omega_\omega\cdot\omega`$ まで延ばす、[BREAK-ja.md](BREAK-ja.md) §2）：

```math
\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta).
```

上半分「$`\le`$」は定理 T-UP、下半分「$`\ge`$」は定理 T-LOW（§3）。Lean には $`\eta = \omega^2`$ までの帰納法があり、
段は仮定（`ConjT.lean`、`LowerT.lean`）。

| $`\eta`$ | 点 | 項 |
|---|---|---|
| $`0`$ | $`\upsilon_1`$ | $`\psi_{\Omega_1}(\Omega_\omega)`$ |
| $`1`$ | $`\upsilon_2`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta)`$ |
| $`2`$ | $`\upsilon_3`$ | $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot 2)`$ |
| $`\omega`$ | $`\upsilon_\omega`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1})`$ |
| $`\omega+1`$ | $`\upsilon_{\omega+1}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1} + \theta)`$ |
| $`\omega\cdot 2`$ | $`\upsilon_{\omega\cdot 2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+1}\cdot 2)`$ |
| $`\omega^2`$ | $`\upsilon_{\omega^2}`$ | $`\psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+2})`$ |

出てくるのは $`\psi_{\Omega_1}`$、$`\psi_{\Omega_2}`$、$`\Omega_\omega`$ だけ。$`\upsilon_{\omega\cdot\omega}`$ より下では到達不能基数は
要らない。素朴な予想 $`\upsilon_\iota = \psi_{\Omega_1}(\Omega_\omega\cdot\iota)`$ は $`\iota = 2`$ から
大きすぎる（Lean：$`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$）。$`+\theta`$ の理由：STEP の証明で、段 0 の符号
$`\mathrm{code}_0`$ は $`\theta`$ より下にとどまる。[R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の翻訳
`por/tr3.py` も、定理 S の行列で同じ点を与える（確認済み）。

## 5. 道筋：補題の木

道は 3 つ：B は上界、A は全部の解析、L は下界。

- **W** Wilken の主張、$`\mathrm{Core}(R_2^+) = \psi_{\Omega_1}(I_\omega)`$ — 未解決
  - **Low** $`\upsilon_{\omega\cdot\omega}`$ より下、$`R_2^C`$ と $`R_2^S`$ で — 証明済み（定理 LOW）
    - 予想 U — 証明済み（STEP、T-UP）
    - 定理 T、$`\eta \lt \Gamma_0`$ での正確な名前 — 証明済み（T-UP、T-LOW）
    - $`\mathrm{Core}(R_2^S)`$ が $`\upsilon_{\omega\cdot\omega}`$ 全体を含む — 証明済み（CORE-S）
    - $`R_2^C`$ で $`\upsilon_{\omega^3}`$ まで、FRAG なしで — 証明済み（CORE-C3、PT）
    - $`R_2^C`$ で $`\Phi_1`$ まで、$`R_2^C`$ の核は $`\rho_{\Theta_P}`$ まで — 証明済み（T++、PHI、CORE-C$`^O`$、CORE-C$`^+`$。
      [REACHES-ja.md](REACHES-ja.md)）
    - $`R_2^C`$ で $`\Lambda_\varepsilon`$ まで、$`R_2^C`$ の核は $`\rho_{\Theta_A+\omega^2}`$ まで — 証明済み（GEN、NAME-V、NAME-OFFSET、
      CORE-C$`^A`$。[PINS-ja.md](PINS-ja.md)）
    - $`R_2^C`$ の核は $`\rho_{\Theta_{d\omega}}`$ までと、$`\nu_C \gt \nu_P`$ で $`[0, \nu_C]`$ で — 証明済み（CORE-C$`^{d\omega}`$、CAP、NU-CT。[BREAK-ja.md](BREAK-ja.md)）
  - **B** 上界 $`\mathrm{Core}(R_2^+) \subseteq \psi_{\Omega_1}(I_\omega)`$ — 未解決
    - B0 最小の鎖への帰着（定理 CC） — $`R_2^C`$ で証明済み
      - B0-S $`R_2^S`$ で同じこと — 未解決。AGR から出る
        - $`S \Rightarrow C`$ — $`\beta_0`$ まで証明済み（STAGE、FIRST）。$`\beta_0`$ より先は未解決（それだけでは帰納法にならない）
        - 一致する段での $`C \Rightarrow S`$ — $`\le_1`$ は $`\kappa_C`$ より下、極限、$`\alpha+1`$、UPG の下で証明済み。$`\kappa_C`$ より上の
          後続では未解決。$`\le_2`$ は後続と LIM2 で証明済み、$`\omega^\lambda`$ で未解決（DICH）
          - (ii) の型の段での $`\le_2`$：1 つの組と $`\Pi_2`$-UP に帰着（MAX2、RED-d、UPCOPY）、$`\kappa_C`$ より下では予想 CORE-2 と
            同値（EQ-E） — 証明済み。PIN と LOW — 未解決
        - (R) は $`\kappa_C \le_1^S \Omega_1`$ と同値、AGR は (E) かつ (R) と同値 — 証明済み（R-OM）
    - B1 どの長さ $`n`$ でも、$`\psi_{\Omega_1}(I_\omega)`$ より下の鎖を InaccPsi の値で具体的に書く — 未解決。評価には組 1 つともう 1 点で
      足りる（CRIT、[COVER-ja.md](COVER-ja.md) §6.2）が、$`x_F`$ や $`c_0`$ を押さえる InaccPsi の項は証明されていない
      （$`n = 3`$ の予想は §3）。$`m_F`$ の評価は組の列の 1 本の列の評価（[FANFREE-ja.md](FANFREE-ja.md) §4）。評価 $`\iota(\mathrm{CH}_2) \lt t`$ は、ちょうど
      $`t`$ より下の 1 点での 3 つの関係（[FANFREE-ja.md](FANFREE-ja.md) §7.4）
    - B2 $`R_2^+`$ での $`\lt_2`$ の有限集合による判定 — 証明済み（T1、T2）。一様な形（すべての $`k`$ に 1 つの写し）が
      必要条件でもあるかは $`R_2^+`$ で未解決（+ の無い $`R_2`$ では成り立つと Wilken 2021, 6 ページが言う）
    - B3 $`0, +, \le, \le_1, \le_2`$ を保つ基の付け替え — $`R_2^+`$ が骨組み型の所で証明済み（定理 FRAG2。FRAG そのものも
      証明済みで、その写像は代入の写像と等しい、FRAG-SUBST、[BREAK-ja.md](BREAK-ja.md) §4）。骨組みの外では、仮定付きで証明済み（FRAG2-W、FRAG2-C、FRAG2-1E）。$`\upsilon`$ の点でない基をいくつも
      同時に（FRAG-E） — 未解決、とても難しい
    - B4 B3 が動かす点の間の $`\le_2`$ の組 — $`R_2^S`$ で $`\nu_P`$ より下、両方の構造で $`\rho_{\Theta_A+\omega^2}`$ より下で証明済み
      （SKEL、BLK$`^O`$、EQB-A）、$`R_2^S`$ では骨組み型でない最初の点 $`\nu`$ まで（SKEL⁺、FIRST-PAIR）。$`\lt_2`$ の左端はどれも
      $`\lambda`$ が極限の $`\upsilon_\lambda`$（LEFT。今は仮定なし：INC1 と NOBAD、
      [BREAK-ja.md](BREAK-ja.md) §1）。$`R_2^S`$ では、どの可算順序数でも、どの組も標準の組か 2 つの
      やり直しの点を結ぶ組なので、$`R_2^S`$ で RIGHT（どの右端も $`\upsilon`$ の点）が成り立つ（SKEL$`^\infty`$、[COVER-ja.md](COVER-ja.md) §5.1）。
      $`\nu`$ より上のやり直しの点の間の組の全体と、$`\beta_0`$ より上の $`R_2^C`$ の RIGHT — 未解決
    - B5 B2 + B3 + B4 を組み立てる — 形だけ
    - B-PT 証明論の別の道：到達不能基数 $`n`$ 個の理論が「長さ $`n`$ の鎖がある」を証明する — 未解決。
      $`\lt_2`$ の集合論的な十分条件が要るが、知られていない
  - **A** 全部の解析 — 未解決
    - A1 どの基の上でも、すべての $`\Omega_\xi`$ と $`I_n`$ のつぶす関数を同時に定義した包の系を作り、InaccPsi と比べる
      — 未解決、難しい（STEP の写像 $`B`$ が、$`\Omega_\omega`$ より下で片向きにこれをする）
    - A2 上限までの $`R_2^+`$ の $`\le_1`$、$`\le_2`$ の構造定理（Wilken 2021, Thm 4.2 の類似）。
      [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の結果は、$`\upsilon_{\omega^3}`$ より下でのこの定理。定理 BLK$`^O`$ が
      正確な届く先とともに $`\Lambda_\varepsilon`$ まで、定理 EXACT-A が $`\Theta_A`$ まで延ばし（[PINS-ja.md](PINS-ja.md)）、$`\Theta_A`$ での値と
      目印 $`\Theta_\delta`$、$`\Theta_{d\omega}`$（[BREAK-ja.md](BREAK-ja.md) §4）、定理 SKEL が $`R_2^S`$ で $`[0, \nu_P)`$ で与え（[REACHES-ja.md](REACHES-ja.md)）、
      SKEL⁺ が $`\nu`$ まで与え（[BREAK-ja.md](BREAK-ja.md) §2）、$`R_2^S`$ の段 0 の記述はどの可算順序数でも成り立つ（SKEL$`^\infty`$、[COVER-ja.md](COVER-ja.md) §5.1）。入れ子の組のどの段でも最初のブロック（LIFT-0、
      [BREAK-ja.md](BREAK-ja.md) §5）、$`T_\omega`$ より下のどの段のどのブロックも（SH、[BREAK-ja.md](BREAK-ja.md) §7.1） — 証明済み。各段の順序型
      （$`o_k = \omega`$。隙間の間の有限の基の付け替え GI と同じ） — $`R_2^C`$ では証明済み（定理 O$`^C`$、[BREAK-ja.md](BREAK-ja.md) §8.1、
      査読 1 回）、$`R_2^S`$ では未解決（Carlson の最小性の $`R_2^S`$ の形と 1 つの止める命題に帰着、[COVER-ja.md](COVER-ja.md) §4。その最小性は
      $`\beta_0`$ まで成り立つ、§5.4）。段 2 の隙間の中の NOLIM — $`R_2^C`$ では証明済み（NOLIM$`^C`$、[COVER-ja.md](COVER-ja.md) の §3 と §5.1）、
      $`R_2^S`$ では幽霊が無ければ証明済み、幽霊があれば $`\beta_0`$ より上で未解決。
      届く先と名前 — 未解決、とても難しい
    - A3 最小の実現を項で書く — 未解決
    - A4 **予想 CH**：長さ $`k+2`$ の最小の鎖には到達不能基数が $`k`$ 個要る — 予想
    - A5 上限より下のどの項も、あるパターンの値 — 未解決
    - A6 どこでも $`R_2^S = R_2^C`$ — 未解決（$`\beta_0 \gt \upsilon_{\omega\cdot\omega}`$ より下では一致）。その最初の場合 $`\nu_C = \nu_S`$ は 1 つの $`\Sigma_2`$ の
      命題（EQ）で、最初のブロックで証明済みの区間の条件 SC から出る（[COVER-ja.md](COVER-ja.md) §6.3）。SC は各区間の最初の部分で
      概略の水準で成り立ち（[FANFREE-ja.md](FANFREE-ja.md) §3）、今は臨界な添字の最初の極限より下で証明済み（[FANFREE-ja.md](FANFREE-ja.md) §7.3）
    - A7 $`R_1^+`$ の相対化したパターンと、順序数とパターンの間の一様な対応（Wilken が予告） — 証明済み（RC-PIN、RC、U、
      UNIF。[PINS-ja.md](PINS-ja.md) §1。閉包は有限（CL-FIN）で、具体的なピンのパターン（EXPL）、[BREAK-ja.md](BREAK-ja.md) §4）。
      対応が初等再帰的であること — 概略だけ
  - **L** 下界 $`\psi_{\Omega_1}(I_\omega) \subseteq \mathrm{Core}(R_2^+)`$ — 未解決
    - L0 $`R_2^C`$ では「どの $`\gamma \lt \psi_{\Omega_1}(I_\omega)`$ も、ある $`\max C^*_n`$ より下」と同値 — 証明済み
    - L-CERT $`\theta_0`$ より下：帰着は証明済み（I-FREE、OE、EPS-RED、FS-OE、RED-BMS、S-RED、MU-A、MU-B、UNIF-V）。
      MU-0 と MU-B0 も（段 0 の (M4)。核には何も足さない）。残り：段 1 以上の (M4)、(M1)–(M3)、SRO 未満での局所的な段
      — 未解決（これらがあれば最初の扇に到達不能基数が要る、RED-HM、[COVER-ja.md](COVER-ja.md) §5.3）。SRO でのいちばん上の段と、いくつかの
      一様な段の族 — 具体的なパターンについて証明済み（[COVER-ja.md](COVER-ja.md) §6.1）。$`V_3`$ より上の標本の決まらない
      26 個の極限の跳び — 証明済み（[FANFREE-ja.md](FANFREE-ja.md) §1）。SRO より下の標本の 3,166 個のうち 459 個（IDX-ADD を含む）での、すべての $`n`$ での段 — 証明済み（[FANFREE-ja.md](FANFREE-ja.md) §7.1）。
      SRO より下のすべての行列での段と、すべての項の上の行列を使わない写像 — 未解決（値が L1p の無いパターンなら $`\iota(\mathrm{CH}_2) \ge \theta_0`$ が出る、[FANFREE-ja.md](FANFREE-ja.md) §7.2）
    - L-CERT $`[\theta_0, \psi_{\Omega_1}(I_0))`$ とその上 — 未解決
    - L-BMS $`\Phi_3`$ を通す道 — 止まっている：DOM₂ により、長さ 3 の鎖の無い $`\Phi_3`$ のパターンは $`m_3`$ より下にとどまり、
      $`\Phi_3`$ が出力する関係にはそういう鎖が決して無い（定理 A、証明済み。閉じた関係では BAR_R、確認済み）
  - **わきの葉**
    - **DOM₂** — 証明済み（SHARP も）。どの $`k`$ でも DOM$`_k`$ — 予想
    - $`C^*_3`$ の場所を見つける — 未解決（予想 C3′ は §3、その導き方は否定された。分かっていること：$`m_3 \ge \Lambda_\varepsilon`$、
      骨組みは $`m_3`$ より下で終わる。届く先だけの道はうまくいかない（NO-PROMOTE）。鎖とは極限が左端である扇（CF）。
      $`c_0, c_1, c_2`$ は集まり $`C_{\omega^\omega}`$ の極限点なので C3′′ は偽（C3-VEB、C3′′-FALSE。[PINS-ja.md](PINS-ja.md) §4、
      [BREAK-ja.md](BREAK-ja.md) §3）。段の極限はどの組にも入らず、$`R_2^C`$ では最初の扇は $`m_3`$ より下（LIM-CAP、DOM_F。[BREAK-ja.md](BREAK-ja.md) §6）。最初の
      扇は $`T_\omega`$ より上で、後の元は 2 つ、$`R_2^C`$ では開いている（FAN-CAP、OPEN-C、LONG-NEST。[BREAK-ja.md](BREAK-ja.md) §7.4）。$`R_2^C`$ では
      鎖の底はちょうど無限の閉じた扇を持つ核の点で、最小の閉じた $`n`$ 扇は $`m_3`$ より下にとどまる（CP3、FIN-FAN）。最小の扇は記述でき、
      順序型は $`\omega^2`$（FS、OF。[COVER-ja.md](COVER-ja.md) の §2 と §5.2）、$`m_F \gt \nu_C`$（[COVER-ja.md](COVER-ja.md) §6.4）。$`m_F`$ は組の列の 1 本の列の点の極限で、
      $`\sigma_N = m_F`$（[FANFREE-ja.md](FANFREE-ja.md) §4）。$`c_2 \lt \omega_1^{CK}`$）
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
(1,1,0)(2,2,1)。値の状態：「証明」= $`V`$ より下の定理 S。「FRAG」= 補題 FRAG を使う $`V_3`$ より下の定理 S（FRAG は証明済みになったので、この行も証明済み）。
「数値」= 数値で確かめただけ。一致：同じ $`J`$ に変換される読み方。

| # | 名前 | M | J | 値 | 一致 |
|---|---|---|---|---|---|
| 1 | υ₁ | `Z` | `p0(W_w)` | 証明 | tr3, Ytosk |
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

BHO は Bachmann–Howard 順序数、`phi(1,W+1)` は $`\varepsilon_{\Omega_1+1}`$。1–6、11–18、20–23 行目の名前は
$`\eta \lt \Gamma_0`$ の $`\upsilon_{1+\eta}`$ なので、そこでは「名前 = $`J`$」が定理 T で証明済み。24–26 行目は $`\eta \ge \Gamma_0`$。
26 行目の項が $`\Xi_1`$ であることは証明済みになった（定理 T++、[REACHES-ja.md](REACHES-ja.md) §2）。
「値」の列は、$`\Phi_3(M)`$ の点がその名前かどうかを言う。

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
- **LOW-STEP の写像 $`E`$。** ランダムな 8 回（$`\eta = 0, 1, 2`$、段は 5 まで、それぞれ約 40 万–50 万組）と、小さな項
  すべての 7 回（876 万組まで）：順序の誤り 0、どの像も定義域に入る。査読者自身の 12 回（$`\eta`$ は $`\omega^2`$ まで、
  もっと大きな $`\sigma`$、強臨界でない $`\varepsilon`$ 数の $`\sigma`$、段は 6 まで。それぞれ 77 万–83 万組）：誤り 0。壊した版
  （$`F`$ 無し、$`\Omega^2`$ の頭無し、$`\varphi`$ の引数の入れ替え）は落ちる。
- **$`B`$ の 2 回目の査読。** 自分のコード。ランダムな 14 回（1,117,200 組）と網羅的な 7 回（11,197,771 組）、
  $`A = A_0, A_1, A_{\omega+1}, A_{\omega^2}`$：順序の誤り 0、標準形でない像 0、上限の破れ 0。
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
- **MU-B の写像 $`\mu_B`$。** $`G_B`$ のランダムな 17,736 項と、査読者の作った 104,071 項：順序の誤り 0、どれも SRO より下、
  像はどれも標準形（yaBMS）。証明書：$`G_B`$ のランダムな標本（10 列以下）の隣り合う 300 組のうち 271 組に証明書があり
  再生した。29 組は未決、反証は無い。逆順の 30 組：0。
- **$`m_3`$ より下の鎖**（2026-10）。「パターンの点 $`\lt m_3`$」の証明書 6 個を再生した。その中に $`\Phi_3(\mathrm{SRO})`$ と
  $`\Phi_3((0,0,0)(1,1,1)(2,2,2)(3,3,3))`$ がある。査読者は、長さ 2 の鎖を別々に 2、3、4 個持つパターンを足した。逆の順序の
  証明書は 45 秒以内に見つからなかった。
- **DOM₂。** 予想どおりの順序「長さ 3 の鎖の無いパターンは $`m_3`$ より下」の証明書が 4 つの形で見つかり、逆向き 3 つは
  それぞれ 40 秒以内に見つからなかった。$`\Phi_3(M)`$ の最長の鎖：$`(0,0,0)(1,1,1)(2,2,2)(3,3,3)`$ からの 3,875 個の行列
  （行 $`\le 3`$、列 $`\le 24`$）で 2。
- **土台の写像 $`\mu_0`$（MU-B0）。** $`G_{B0}`$ のランダムな項 6,480 個。標本ごとに土台の上のランダムな順序を保つ写像を使う：
  順序の誤り 0、標準形でない像 0（yaBMS）、すべて SRO より下。土台の写像をかき混ぜると、同じ標本で順序の誤り 111、
  標準形でない像 182 が出るので、この検査は失敗しうる。査読者の新しい標本（400 項）：誤り 0。
- **$`V_3`$ より上の局所的な段。** $`G_{B0}`$ の像の隣り合う 160 組（10 列以下）：134 組に証明書があり再生した（査読者も
  再生）。26 組は未決（どれも、最後の列が土台の項から来る極限）、反証は無い。逆順の 30 組：0。$`V_3`$ そのもの：
  $`N \le 10`$ で 11 個のうち 11 個の証明書を再生した。今は 26 組のうち 5 組に再生した証明書があり、もう 1 組は手で証明済み、20 組は
  未決のまま（[COVER-ja.md](COVER-ja.md) §6.1）。今は 26 組すべてが手で証明済みで、手の証明は証明書として再生できる（[FANFREE-ja.md](FANFREE-ja.md) §1）。
- **$`\Phi_3`$ の鎖。** 定理 A、BAR、BAR_R、「閉じた関係 = 出力の関係」、「閉じた関係の最長の鎖は 2」：6 つの出発点からの
  12,963 個の行列で失敗 0（入れ子の組 78,991 個）。査読者：ランダムな入力 229,888 個で定理 A の失敗 0。BAR_R はそのうち
  824 個で破れた（再実行では 664 個）が、どれも標準形ではない。

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
この帰結は**証明されていない**：$`\Phi_3`$ が出力する関係には長さ 3 の鎖が無い（定理 A、証明済み）が、$`m_3`$ で抑えるには
「$`\Phi_3(M)`$ はパターン」（未解決）も要り、しかも $`R_2^C`$ だけの話である。

## 7. ファイル

| ファイル | 何を証明するか |
|---|---|
| [CountSeg.lean](CountSeg.lean) | 補題 L、`bounded_inter_Om1`、`vals_inter_Om1`、`three_bounds` |
| [LowSeg.lean](LowSeg.lean) | 補題 IS と補題 CONT |
| [ConjT.lean](ConjT.lean) | 定理 T-UP の InaccPsi 側：$`A_\eta`$ での (HA)、STEP を仮定とした $`\eta = \omega^2`$ までの帰納法、そこからの予想 U、補題 M の算術 |
| [LowerT.lean](LowerT.lean) | 定理 T-LOW の InaccPsi 側：LOW-0 と LOW-STEP を仮定とした $`\eta = \omega^2`$ までの帰納法と、両方の半分からの定理 T |
| [LowTerms.lean](LowTerms.lean) | §4 の 7 つの項 $`u(\eta)`$：標準形、値、順序、$`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ |

$`R_2^+`$ そのものについては、Lean には何も無い。$`\upsilon_{\omega^3}`$ より上の結果は 2 ページ目
[RESTARTS-ja.md](RESTARTS-ja.md) に、$`\Xi_\omega`$ より上の結果は 3 ページ目 [REACHES-ja.md](REACHES-ja.md) に、$`\Lambda_\varepsilon`$ より先の
結果は 4 ページ目 [PINS-ja.md](PINS-ja.md) に、骨組みが終わる所とその上の段の結果は 5 ページ目 [BREAK-ja.md](BREAK-ja.md) に、
被覆に対する最小性による結果と段 0 の記述（5 回目から 7 回目）は 6 ページ目 [COVER-ja.md](COVER-ja.md) に、8 回目と 9 回目は 7 ページ目 [FANFREE-ja.md](FANFREE-ja.md) にある。

## 8. 文献

- T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001).
- T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009).
- T. J. Carlson, G. Wilken, "Normal forms for elementary patterns", JSL 77 (2012).
- G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
- G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
- A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined θ-functions", MLQ 57 (2011).
- G. Wilken, "A glimpse of Σ₃-elementarity" (2020).
- G. Wilken, "Pure Σ₂-elementarity beyond the core", APAL 172 (2021).
- W. Buchholz, "A new system of proof-theoretic ordinal functions", APAL 32 (1986).
- W. Buchholz, "A simplified version of local predicativity" (1992).
- W. Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof Theory (1998), Ch. IV.
