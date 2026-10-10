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
[REACHES-ja.md](REACHES-ja.md)）。次に $`\Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$ まで（[PINS-ja.md](PINS-ja.md) §3）、次に $`\rho_{\Lambda'+\omega^2}`$ まで
（[FANFREE-ja.md](FANFREE-ja.md) §10.4）、$`\rho_{\Lambda_{\mathrm{fp}}+\omega^2}`$ と $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ まで（[VEBLEN-ja.md](VEBLEN-ja.md) §1、§8）成り立ち、次に

```math
\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)
```

まで（査読 2 回。[THETA-ja.md](THETA-ja.md) §1、§9.1）、次に $`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$ として $`X_2 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$ まで
（査読 2 回。$`X_2 = \nu_P`$ は査読 1 回）、次に $`X_3 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$ まで（査読 1 回、[THETA-ja.md](THETA-ja.md) §9.1）
成り立ち、次に

```math
X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2),\quad G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})
```

まで成り立つ（査読 1 回、FRAG 無し、[SHIFT-ja.md](SHIFT-ja.md) §1）。FRAG のもとで $`X_5`$ まで（[SHIFT-ja.md](SHIFT-ja.md) §8.1）、$`X_8`$ まで（査読 2 回、[SHIFT-ja.md](SHIFT-ja.md) §9.1）、$`X_9 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+\Omega_1} + \omega^{G(\Omega_1)+1} + \omega^{G_2+1})`$ まで（$`G(\Omega_1) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_1})`$。
査読 2 回、[SHIFT2-ja.md](SHIFT2-ja.md) §1.1、§2.1）、最初の添字の不動点を越えて $`X_{11}`$ まで（[SHIFT2-ja.md](SHIFT2-ja.md) §2.1）、$`X_{12}`$ まで（[SHIFT2-ja.md](SHIFT2-ja.md) §3.1）、$`X_{13}`$ まで（[SHIFT3-ja.md](SHIFT3-ja.md) §1.1）、$`X_{14}`$ まで（[SHIFT3-ja.md](SHIFT3-ja.md) §2.1）、$`X_{15}`$ と $`X_{16}`$ まで（査読 2 回、[SHIFT4-ja.md](SHIFT4-ja.md) §1.1、§1.4、§2.1）、$`X_{17}`$ まで（[SHIFT4-ja.md](SHIFT4-ja.md) §2.1）、$`X_{18}`$ まで（査読 2 回。[SHIFT4-ja.md](SHIFT4-ja.md) §2.2、[SHIFT5-ja.md](SHIFT5-ja.md) §1.1）、$`X_{19}`$ まで（[SHIFT5-ja.md](SHIFT5-ja.md) §1.1）、$`\hat\zeta_H = \theta_3\cdot\Omega_3 + \omega^{\hat g_3+g_3}`$ として $`X_{21} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_H + \omega^{G(\hat\zeta_H)+1}\cdot 2)`$ まで
（査読 2 回。[SHIFT5-ja.md](SHIFT5-ja.md) §2.1、[SHIFT6-ja.md](SHIFT6-ja.md) §1.1）、$`X_{22}`$ まで（[SHIFT6-ja.md](SHIFT6-ja.md) §1.1）、そして

```math
X_{23} = \psi_{\Omega_1}(\Omega_\omega + \hat\zeta_{23} + \omega^{G(\hat\zeta_{23})+1}\cdot 2),\quad \hat\zeta_{23} = \theta_4\cdot\Omega_4 + \varepsilon_{\hat g_4+1}
```

まで成り立つ（[SHIFT6-ja.md](SHIFT6-ja.md) §2.1、§3.1。$`X_{22}`$ と $`X_{23}`$ は、それらのクッションの蓋が使う長いちょうどの届く先の進行を止める点 B-1 が直るまで、書いたままでは
未証明だった。直しについて査読 1 回、[SHIFT6-ja.md](SHIFT6-ja.md) §3.1。$`\theta_3 = \psi_{\Omega_4}(\Omega_\omega)`$、$`\theta_4 = \psi_{\Omega_5}(\Omega_\omega)`$、$`g_3`$、$`\hat g_3`$、$`\hat g_4`$ と、下で使うほかの ^ の付いた乗数は
[SHIFT5-ja.md](SHIFT5-ja.md) と [SHIFT6-ja.md](SHIFT6-ja.md) で定義する）。さらに FRAG のもとで、主張は

```math
L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P'),\quad P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)
```

まで成り立つ（査読 1 回、[SHIFT7-ja.md](SHIFT7-ja.md) §1.1）。これはちょうど骨組み型でなくなる最初の点：FRAG のもとで $`\nu_C = \nu_S = L(\omega+1)`$（査読 1 回、[SHIFT7-ja.md](SHIFT7-ja.md) §2.1）。だから
**FRAG のもとで、$`R_2^C`$ での Wilken の主張は $`[0, \nu_C]`$ で成り立ち**、2 つの定義の骨組み型でなくなる最初の点は同じで、仮定 LOW（$`\nu_C \le \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$）は偽。FRAG 無しでは、核の側だけなら $`R_2^C`$ でさらに先、
$`[0, \nu_C]`$ で証明済み。$`\nu_C`$（FRAG 無しで $`\ge X_4`$）は $`R_2^C`$ が骨組み型でなくなる最初の点（[BREAK-ja.md](BREAK-ja.md) §2）。

## 3. 証明済みのこと

**まとめ。** $`\upsilon_{\omega\cdot\omega}`$ より下では、主張は $`R_2^C`$ でも $`R_2^S`$ でも成り立つ：$`\upsilon_{\omega\cdot\omega}`$ 未満の
どの順序数も核に入り、しかも、つぶす引数がすべて $`I_\omega`$ 未満の InaccPsi の標準形の可算な値である（下の定理 LOW）。
Wilken の点には正確な名前がある：$`\eta \lt \Gamma_0`$ で $`\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$（定理 T、§4）。のちに $`\upsilon^*`$ より下の
すべての $`\upsilon`$ 点に（定理 GEN）、$`\eta \lt \Omega_\omega`$ に（GEN⁺、GEN-EXT の場合）広がり、今は $`I_\omega`$ の先まで届く類のどの $`\eta`$ にも広がった（GEN-ALL、[SHIFT5-ja.md](SHIFT5-ja.md) §1.3）。$`R_2^C`$ では主張は $`X_4`$ まで、FRAG のもとで $`\nu_C = L(\omega+1)`$ まで成り立ち、核は $`[0, \nu_C]`$ を含む（§2）。
研究は、査読された 4 つの論文ずつの回で進んだ。このページには 1 回目の結果がある（その一部は [ROUND1-ja.md](ROUND1-ja.md)）。のちの回はページ
[RESTARTS-ja.md](RESTARTS-ja.md)、[REACHES-ja.md](REACHES-ja.md)、[PINS-ja.md](PINS-ja.md)、[BREAK-ja.md](BREAK-ja.md)、[COVER-ja.md](COVER-ja.md)、[FANFREE-ja.md](FANFREE-ja.md)、[VEBLEN-ja.md](VEBLEN-ja.md)、
[THETA-ja.md](THETA-ja.md)、[SHIFT-ja.md](SHIFT-ja.md)、[SHIFT2-ja.md](SHIFT2-ja.md)、[SHIFT3-ja.md](SHIFT3-ja.md)、[SHIFT4-ja.md](SHIFT4-ja.md)、[SHIFT5-ja.md](SHIFT5-ja.md)、[SHIFT6-ja.md](SHIFT6-ja.md)、[SHIFT7-ja.md](SHIFT7-ja.md) にある。1〜12 回目のまとめは [THETA-ja.md](THETA-ja.md) §8.1 に、13〜31 回目のまとめは [ROUND2-ja.md](ROUND2-ja.md) §1 にある。未解決：$`R_2^C`$ では $`\nu_C = L(\omega+1)`$ より上（FRAG 無しでは $`X_4`$ より上）、
$`R_2^S`$ では $`\upsilon_{\omega^3}`$ より上の両方の半分；$`\nu`$ より上の $`R_2^S = R_2^C`$（最初の場合 $`\nu_C = \nu_S`$ は FRAG のもとで証明済み）；$`\theta_0`$ より下の下界；
最初の扇に到達不能基数が要るか；$`C^*_3`$ の InaccPsi による上からの評価（$`C^*_3`$ は $`\omega_1^{CK}`$ より下、Carlson 2009, Thm 15.2）。

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
さらに $`[0, \rho_{\Theta_A+\omega^2})`$ まで（[PINS-ja.md](PINS-ja.md) §2）。さらに $`[0, \rho_{\Theta_{d\omega}})`$ まで、さらに $`\nu_C \gt \nu_P`$ で $`[0, \nu_C]`$ まで（[BREAK-ja.md](BREAK-ja.md) §2、§4）、今は $`\nu_C \ge X_4`$（[SHIFT-ja.md](SHIFT-ja.md) §1）、FRAG のもとで §2 のそれぞれの点 $`X_5, \dots, X_{23}`$ について $`\nu_C \ge X_n`$（[SHIFT6-ja.md](SHIFT6-ja.md) §2.1、§3.1）、そして $`\nu_C \ge L(\omega+1)`$（[SHIFT7-ja.md](SHIFT7-ja.md) §1.1）、そして $`\nu_C = L(\omega+1)`$（そこの §2.1）。

- 補題 PT、定理 CORE-C3（FRAG なしで、$`\upsilon_{\omega^3}`$ 以下のどの順序数も $`\mathrm{Core}(R_2^C)`$ に入る）とその系 $`m_3 \ge \upsilon_{\omega^3}`$（どれも査読 1 回）は
  [ROUND2-ja.md](ROUND2-ja.md) §2 にある。

**$`R_2^S`$ と $`R_2^C`$**（2026-10）。これらの結果は今は [THETA-ja.md](THETA-ja.md) §8.2 にある：2 つの構造が食い違う最小の段 $`\beta_0`$ と、
それより上のすべてに $`\le_1^X`$ な最小の $`\kappa`$ である $`\kappa_X`$；補題 STAGE と系 FIRST（右端が $`\beta_0`$ 以下の $`R_2^S`$ の関係はどれも $`R_2^C`$ で成り立ち、
今は $`\beta_0 \ge \nu_C \gt \nu_P`$）；定理 LOC と $`\nu_C = \nu_S`$ の帰着（今はねじれた上向きの規則に、[THETA-ja.md](THETA-ja.md) §4。$`\nu_C = \nu_S`$ そのものは今は FRAG のもとで証明済み、[SHIFT7-ja.md](SHIFT7-ja.md) §2.1）；補題 UPG；KAPPA と CORE-EQ
（$`\max(\kappa_S, \kappa_C) \le \beta_0`$、つまり AGR なら、2 つの核は等しい）；一致する段での逆向き $`C \Rightarrow S`$（CORE-1、LIM1、ONE-POINT、SUCC2、LIM2）；
DICH；R-INC；型 (ii) の段（MAX2、RED-d、FIRST2、UPCOPY、予想 CORE-2 を含む EQ-E、R-OM、未解決の段 PIN と LOW）。

**[ROUND1-ja.md](ROUND1-ja.md) に移したもの**（1 回目、2026-10）：$`R_2^S`$ での有限集合による判定 T1、PR、T2、CMP（そこの §1）。長さ 3 の鎖を具体的に求める結果、
その中に ELEM、CLUB-1、CHAINS-S、HIGH、LOCAL-2、CHANG-2、SC2、I0-NOT-SIGMA2、REFORM、NO-PROMOTE、補題 K、COLLAPSE-FAIL（進行を止める点つき）（そこの §2）。
下界に向けた帰着 I-FREE、OE、EPS-RED、FS-OE、RED-BMS、S-RED、MU-A、UNIF-V、MU-B（核に使うことに対する進行を止める点つき）、MU-0、MU-B0
（そこの §3。下の $`G_B`$ は MU-B の断片）。$`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$ と書く。補題 I-FREE により、到達不能基数の記号を含まない可算な標準形は、ちょうど $`\theta_0`$ より下のもの。

**鎖。** 長さ $`n`$ の鎖は、互いに $`\le_2`$ な $`n`$ 個の加法的主要数。$`C^*_n`$ は各点ごとに最小のもの。

- **定理 CC**（$`R_2^C`$ で）。$`\mathrm{Core}(R_2^C) = \sup_n \max C^*_n`$。加法的主要数を $`n`$ 個持つパターンの最小の実現は
  $`\max C^*_{n+1}`$ より下。（$`R_2^S`$ では未解決。AGR があれば核は同じ。）
- **定理 DOM₂**（2026-10、$`R_2^C`$）。$`C^*_3 = \{c_0 \lt c_1 \lt c_2\}`$、$`m_3 = \min\{m : m \le_1 c_0\}`$ とする。長さ 3 の鎖を
  持たないパターンの最小の実現は $`m_3`$ より下で、$`m_3 \lt c_0`$。**定理 SHARP**：長さ 3 の鎖を持たない isominimal な
  集合の合併は、ちょうど $`[0, m_3)`$。**DOM₁′**：$`\lt_2`$ の組を持たないパターンで同じこと。その合併は $`[0, m_2)`$、
  $`m_2`$ は $`\min C^*_2 = \upsilon_\omega`$ の最小の $`\le_1`$ の前の元。引用した $`R_1^+`$ の核と定理 A・EQ を仮定すれば
  $`m_2 = \upsilon_1`$。
- $`C^*_3`$、扇、組の鎖 $`\mathrm{CH}_k`$ についての事実（2026-10）：$`m_3`$、$`c_0`$、扇、$`m_F`$ の下からの評価と、$`\iota(\mathrm{CH}_k)`$ の素の評価は
  [ROUND2-ja.md](ROUND2-ja.md) §3 にある。いちばん新しい素の評価は、札の飾りの区域による $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$
  （[SHIFT7-ja.md](SHIFT7-ja.md) §2.3。前は、どの有限の段の段階の札で $`\psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega)`$、そこの §1.3、§2.3。段階の札を符号の組の中の点にして $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$、[SHIFT6-ja.md](SHIFT6-ja.md) §3.3。$`\psi_{\Omega_1}(\Omega_\omega\cdot\Theta_1)`$ と、鎖の数を増やして $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$、そこの §1.3）。また $`C^*_2 = \{\upsilon_\omega, \upsilon_{\omega+1}\}`$。
- 補題 TOP2（$`m_3`$ は長さ 2 の鎖の極限）、補題 REL（$`\psi_{\Omega_1}(A)`$ より上でやり直すと 1 段の費用は $`+\theta`$）、小さな補題 PRINC、ISO-UNION、HULL、DOM₁、
  $`\Phi_3`$ が作る鎖（定理 A：出力の関係に長さ 3 の鎖は無い。定理 B、系 C、補題 LAM、BAR_R、CONE）は [ROUND2-ja.md](ROUND2-ja.md) §4 にある。

**証明されていないこと：**

- **$`R_2^C`$ で FRAG のもとで $`\nu_C = L(\omega+1)`$ より上（FRAG 無しで $`X_4`$ より上）、$`R_2^S`$ で $`\upsilon_{\omega^3}`$ より上での主張**、両方の半分（$`\nu_C`$ より上では構造は骨組み型でない。主張を $`\nu_C`$ まで与える InaccPsi による
  上からの評価 $`\nu_C \le L(\omega+1)`$ は今は FRAG のもとで証明済み、[SHIFT7-ja.md](SHIFT7-ja.md) §2.1。それには名前の付いた 1 つの組での 2 つの $`\le_1`$ の命題 (P) と (Q) だけが要り、どちらも長いやり直しの届く先に
  ついての命題、[SHIFT-ja.md](SHIFT-ja.md) §1。(Q) は左端より下の届く先の知られた上からの評価からは出ない、§8.1。(P) には非可算のずれ、つまり最初の添字の不動点の先を越える届く先が要る、§9.1、[SHIFT2-ja.md](SHIFT2-ja.md) §1.1。道具は今は順序型によるちょうどの蓋とともに $`\theta`$ より下の η ずれまで届き、[SHIFT3-ja.md](SHIFT3-ja.md) §1.1、§2.1、さらに $`\psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ より下の η ずれと $`G(\Omega_3+1)`$ より下の符号まで届き、[SHIFT4-ja.md](SHIFT4-ja.md) §1.1、§1.4、さらに $`G(\hat\zeta_2)`$ より下の符号まで届き、そこの §2.1、§2.2、さらに着地の蓋で $`G(\hat\zeta_\varepsilon)`$ より下の符号まで届き、[SHIFT5-ja.md](SHIFT5-ja.md) §1.1、さらに包の蓋（着地の蓋はもっと上で偽）で $`G(\hat\zeta_H)`$ より下の符号まで届き、そこの §2.1、さらに包の要らない蓋で $`G(\theta_4\cdot\omega^2)`$ より下の符号と $`G(\hat\zeta_{23})`$ より下の符号まで届く、[SHIFT6-ja.md](SHIFT6-ja.md) §1.1、§2.1 と、そこの §3.1 の直し、さらにどの深さでも相対的な遠いピンで $`P'`$ より下のどの符号にも届き、$`\nu_C \ge L(\omega+1)`$ が出る、[SHIFT7-ja.md](SHIFT7-ja.md) §1.1。さらに符号 $`P'`$ での極限の越え方で (P)、ずらしの判定で (Q)、そこの §2.1）。$`\Theta_A`$ より上の
  やり直しの届く先（$`\Theta_A`$ そのものでの届く先は今は分かっている）と、[SHIFT7-ja.md](SHIFT7-ja.md) §2.6、[COVER-ja.md](COVER-ja.md) §9、[BREAK-ja.md](BREAK-ja.md) §10、[PINS-ja.md](PINS-ja.md) §6、[REACHES-ja.md](REACHES-ja.md) §7、[RESTARTS-ja.md](RESTARTS-ja.md) §6 の残り。
- **$`\nu`$ より上の $`R_2^S = R_2^C`$**（その下では FRAG のもとで $`\nu_C = \nu_S`$ なので 2 つは一致する、[SHIFT7-ja.md](SHIFT7-ja.md) §2.1）：$`\le_1`$ の逆向き $`C \Rightarrow S`$ は、$`\kappa_C`$ より上の後続の段で $`\alpha \notin G_C`$ のとき未解決。
  $`\le_2`$ の逆向きは、(ii) の型の段で未解決（$`\Pi_2`$ 文を上向きに移すことが要るが、上向きの 2-反映でも持ち上げでも
  得られない。いまは段ごとに 1 つの組 $`(a^*, \beta)`$ の話で、$`\kappa_C`$ より下では予想 CORE-2 と同値。残りは PIN と LOW）。
  Σ2-GAP、INC、W(C)、(R)、AGR、$`\beta_0 = \infty`$ も未解決（これらの言葉は [THETA-ja.md](THETA-ja.md) §8.2 で定める）。定理 CC とすべての証明書は $`R_2^C`$ の話。
- **$`\theta_0`$ より下の下界**（査読：この目標に向けた止める穴。本文の誤りではない。$`V_3`$ より上の標本の決まらない 26 個の極限の
  跳びは今は証明済み、[FANFREE-ja.md](FANFREE-ja.md) §1。SRO より下の段は今は標本の 3,166 個すべてで、すべての $`n`$ で証明済み、
  [FANFREE-ja.md](FANFREE-ja.md) §7.1、§10.1、[VEBLEN-ja.md](VEBLEN-ja.md) §3、§10、[THETA-ja.md](THETA-ja.md) §3、§9.3、[SHIFT-ja.md](SHIFT-ja.md) §3、§8.3、§9.3、[SHIFT2-ja.md](SHIFT2-ja.md) §1.3、§2.3、§3.3、[SHIFT3-ja.md](SHIFT3-ja.md) §1.3、§2.3、[SHIFT4-ja.md](SHIFT4-ja.md) §1.3、§2.3）：$`\theta_0`$ 未満のすべての
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
- $`\Phi_3(M)`$ がパターンであること。そうなら長さ 3 の鎖は無く（系 C、[ROUND2-ja.md](ROUND2-ja.md) §4）、DOM₂ によりその点は $`m_3`$ より下。出力された関係
  そのものにはそういう鎖は無い（定理 A、証明済み）。閉じた関係では BAR_R（確認済みだけ）。

## 4. Wilken の点の名前（定理 T）

**定理 T**（証明済み。上半分 T-UP は査読 2 回、下半分 T-LOW は査読 1 回）。$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$ として、
どの $`\eta \lt \Gamma_0`$ でも、とくに $`\eta \le \omega^2`$ で。さらに定理 T+（査読 2 回、[RESTARTS-ja.md](RESTARTS-ja.md) §4）により、
$`\iota \mapsto \upsilon_\iota`$ の最初の不動点 $`\Xi_1`$ 未満のどの $`\eta`$ でも（その先は、[REACHES-ja.md](REACHES-ja.md) §2 の定理 T++ が
$`\Phi_1`$ までのすべての $`\Xi_\alpha`$ とその間の点に名前を付け、[PINS-ja.md](PINS-ja.md) §3 の定理 GEN が
$`\upsilon^*`$ より下の $`\upsilon`$ の点に名前を付ける（今は $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ と分かっている、[THETA-ja.md](THETA-ja.md) §1）：標準形を与える $`\eta \lt \Omega_2`$ の集合を $`D`$、
$`D \cap \eta`$ の順序型を $`\iota(\eta)`$ とすると、$`D`$ のどの $`\eta`$ でも $`\psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta) = \upsilon_{1+\iota(\eta)}`$。GEN-EXT がこれを
$`\eta \lt \Omega_\omega\cdot\omega`$ まで延ばす、[BREAK-ja.md](BREAK-ja.md) §2。GEN-EXT の場合である GEN⁺ は、標準形を与えるすべての $`\eta \lt \Omega_\omega`$ の集合でこれを述べる、[THETA-ja.md](THETA-ja.md) §1。そこでは移しのラベルだったが、GEN-EXT を引いて証明済み、[SHIFT4-ja.md](SHIFT4-ja.md) §2.4。GEN-ALL は $`\eta \in \mathrm{Cl}(\Omega_\omega + \theta\cdot\eta, \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta))`$ のどの $`\eta`$ にも広げ、だから $`\psi_{\Omega_1}(I_\omega)`$ もそれ自身 $`\upsilon`$ 点、[SHIFT5-ja.md](SHIFT5-ja.md) §1.3）：

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
    - 定理 T、$`\eta \lt \Gamma_0`$ での正確な名前 — 証明済み（T-UP、T-LOW）。$`\upsilon^\infty \gt \psi_{\Omega_1}(I_\omega)`$ より下のどの $`\upsilon`$ 点の名前 — 証明済み（GEN-ALL。[SHIFT5-ja.md](SHIFT5-ja.md) §1.3）
    - $`\mathrm{Core}(R_2^S)`$ が $`\upsilon_{\omega\cdot\omega}`$ 全体を含む — 証明済み（CORE-S）
    - $`R_2^C`$ で $`\upsilon_{\omega^3}`$ まで、FRAG なしで — 証明済み（CORE-C3、PT）
    - $`R_2^C`$ で $`\Phi_1`$ まで、$`R_2^C`$ の核は $`\rho_{\Theta_P}`$ まで — 証明済み（T++、PHI、CORE-C$`^O`$、CORE-C$`^+`$。
      [REACHES-ja.md](REACHES-ja.md)）
    - $`R_2^C`$ で $`\Lambda_\varepsilon`$ まで、$`R_2^C`$ の核は $`\rho_{\Theta_A+\omega^2}`$ まで — 証明済み（GEN、NAME-V、NAME-OFFSET、
      CORE-C$`^A`$。[PINS-ja.md](PINS-ja.md)）
    - $`R_2^C`$ で $`\rho_{\Lambda'+\omega^2}`$ まで、そこの届く先の閉じた形と $`\Theta_P`$ の名前とともに — 証明済み（NAME-OFFSET-Z、STRUCT′、THETA-P。
      [FANFREE-ja.md](FANFREE-ja.md) §10.4）
    - $`R_2^C`$ で $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ まで、そこの届く先の閉じた形とともに — 証明済み（VEB-THETA、GAM-THETA′、EXACT-G⁺、PSI2⁺、
      NAME-OFFSET-G⁺、STRUCT″。[VEBLEN-ja.md](VEBLEN-ja.md) §1、§8）。$`\Theta_1 = H(\theta)`$ と $`\Theta_A = H(\varepsilon_{\theta+\omega})`$ として $`H(\varepsilon_{\theta+\omega} + \omega^2)`$ まで — 証明済み
      （PAR-SAME と L3、B-PAR、PAR-ψ、H3。THETA1 と THETA-A は査読 2 回。[THETA-ja.md](THETA-ja.md) §1）
    - $`R_2^C`$ で $`\upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$ まで、そして $`\nu_P = X_2`$ まで — 証明済み、査読 2 回（UPS\*、U\*、F1、GEN⁺、SLOW$`_\zeta`$、補題 S、R-CAP、F2。
      [THETA-ja.md](THETA-ja.md) §1、§9.1）。$`\Theta_\delta`$、$`\Theta_{d\omega}`$、$`\Lambda^*`$、$`\nu_P`$ の名前 — 証明済み（SSTEP$`_\zeta`$、HULL-SEG、REAL、BRACKET、NAMES-EQ。
      直した形式的な届く先で。それは査読 2 回。[THETA-ja.md](THETA-ja.md) §9.1、[SHIFT-ja.md](SHIFT-ja.md) §1）。$`\nu_C \ge X_3`$ として $`X_3`$ まで — 証明済み、FRAG 無し（定理 X3）。
      $`\nu_C \ge X_4`$ として $`X_4`$ まで — 証明済み、FRAG 無し（TOP-REG⁺、R-CAP\*、定理 X4。[SHIFT-ja.md](SHIFT-ja.md) §1）。
      $`\nu_C \ge X_5`$ として $`X_5`$ まで — FRAG のもとで証明済み（XA、EXACT-C、PIN-IDX、R-CAP-ξ、FAR、定理 X5。[SHIFT-ja.md](SHIFT-ja.md) §8.1）。
      $`\nu_C \ge X_8`$ として $`X_8`$ まで — FRAG のもとで、あらすじの入力無しに証明済み（OFF、FAR-PIN、TOP-REG-FAR、MULTI-RC、R-CAP-FAR、定理 X8。査読 2 回。[SHIFT-ja.md](SHIFT-ja.md) §9.1）。
      $`\nu_C \ge X_9`$ として $`X_9`$ まで — FRAG のもとで証明済み（OFF-INF、MULTI-RC\*、PHI\*、R-CAP-FAR\*、定理 X9。査読 2 回。[SHIFT2-ja.md](SHIFT2-ja.md) §1.1、§2.1）。
      $`\nu_C \ge X_{11}`$ として $`X_{11}`$ まで — FRAG のもとで証明済み（D′-UNC、DICT、EXACT-V、MULTI-RC$`^U`$、PHI$`^U`$、R-CAP$`^U`$、CEIL$`^U`$、定理 X11。[SHIFT2-ja.md](SHIFT2-ja.md) §2.1）。
      $`\nu_C \ge X_{12}`$ として $`X_{12}`$ まで — FRAG のもとで証明済み（NO-PHI、PSI2-χ、EXACT-O、EXACT-LONG、R-CAP$`^\chi`$、CEIL$`^\chi`$、定理 X12。[SHIFT2-ja.md](SHIFT2-ja.md) §3.1）。
      $`\nu_C \ge X_{13}`$ として $`X_{13}`$ まで — FRAG のもとで証明済み（TOP-REG-FAR′、VEB-THETA$`^\vartheta`$、PSI2-θ、EXACT-O$`^\vartheta`$、R-CAP$`^\vartheta`$、CEIL$`^\vartheta`$、定理 X13。[SHIFT3-ja.md](SHIFT3-ja.md) §1.1）。$`\nu_C \ge X_{14}`$ として $`X_{14}`$ まで — FRAG のもとで証明済み
      （PSI-n、CNST$`^n`$、EXACT-O$`^n`$、R-CAP$`^\theta`$、CEIL$`^\theta`$、定理 X14。[SHIFT3-ja.md](SHIFT3-ja.md) §2.1）。$`\nu_C \ge X_{15}`$ として $`X_{15}`$ まで — FRAG のもとで証明済み
      （CLOSED-REACH、TOP-REG$`^\omega`$、EXACT-CL、$`\zeta^*`$ より下の層、定理 X15。[SHIFT4-ja.md](SHIFT4-ja.md) §1.1）。$`\nu_C \ge X_{16}`$ として $`X_{16}`$ まで — FRAG のもとで証明済み
      （PLATEAU、D-UNC$`^Z`$、θ⁺ の層、R-U、定理 X16。[SHIFT4-ja.md](SHIFT4-ja.md) §1.4。どちらも査読 2 回、§2.1）。$`\nu_C \ge X_{17}`$ として $`X_{17}`$ まで — FRAG のもとで証明済み
      （ROOT-LOC、ENUM、EXACT-CL\*、$`\Omega_3\cdot\omega`$ までの層、定理 X17。[SHIFT4-ja.md](SHIFT4-ja.md) §2.1）。$`\nu_C \ge X_{18}`$ として $`X_{18}`$ まで — FRAG のもとで証明済み
      （PHI-COMM、順序数の側の READ、$`G(\hat\zeta_2)`$ より下の蓋、定理 X18。[SHIFT4-ja.md](SHIFT4-ja.md) §2.2。[SHIFT5-ja.md](SHIFT5-ja.md) §1.1 の直しで査読 2 回）。$`\nu_C \ge X_{19}`$ として $`X_{19}`$ まで — FRAG のもとで証明済み
      （SEP$`^{\mathrm{near}}`$、NO-LIT、EXACT-LONG⁺、FAR-PIN$`^L`$、TOP-REG-LAND、LAND-CAP、定理 X19。[SHIFT5-ja.md](SHIFT5-ja.md) §1.1）。$`\nu_C \ge X_{21}`$ として $`X_{21}`$ まで — FRAG のもとで証明済み
      （THETA$`^G`$、EXACT-LONG$`^G`$、EXACT-F、NO-READL、CAP$`^\sharp`$、定理 X21。[SHIFT5-ja.md](SHIFT5-ja.md) §2.1。[SHIFT6-ja.md](SHIFT6-ja.md) §1.1 の直しで査読 2 回）。$`\nu_C \ge X_{23}`$ として $`X_{22}`$ と $`X_{23}`$ まで — FRAG のもとで証明済み
      （CUSHION、定理 X22、CUSHION$`^\varepsilon`$、定理 X23。長いちょうどの届く先は着地の符号で直した：AGREE、EXACT-LONG$`^{(3)\sharp}`$。[SHIFT6-ja.md](SHIFT6-ja.md) §1.1、§2.1、§3.1。直しについて査読 1 回）。$`\nu_C \ge L(\omega+1)`$ として $`L(\omega+1)`$ まで — FRAG のもとで証明済み
      （FAR-PIN$`^{L,\mathrm{rel}}`$、LAND$`^\omega`$、$`P'`$ より下の EX$`^w`$ と CAP-0、CAP-1、NU-LOW″⁺。[SHIFT7-ja.md](SHIFT7-ja.md) §1.1。査読 1 回）。**$`\nu_C = \nu_S = L(\omega+1)`$ で $`[0, \nu_C]`$ 全体で — FRAG のもとで証明済み**
      （CROSS-LIM、TC⁺$`^\omega`$、EMB、ONTO-FIN、PAIR、UP、NU、LC-STRICT。[SHIFT7-ja.md](SHIFT7-ja.md) §2.1。査読 1 回。下の半分の 1 つの穴の直しは査読 2 回）
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
    - B-NU $`\nu_C`$ の InaccPsi による上からの評価 — FRAG のもとで証明済み：$`\nu_C \le \nu_S \le L(\omega+1)`$（SHIFT による PAIR、CROSS-LIM、TC⁺$`^\omega`$、EMB、ONTO-FIN とあわせて。[SHIFT7-ja.md](SHIFT7-ja.md) §2.1。査読 1 回）。これは名前の付いた 1 つの組での 2 つの $`\le_1`$ の命題 (P) と (Q) に帰着し、どちらも
      長いやり直しの届く先についての命題（NU-MIN、CPB-S。ずらしの判定 SHIFT は証明済み、名前の付いた場合は未解決。[SHIFT-ja.md](SHIFT-ja.md) §1）。両方を満たす組の右端は
      FRAG のもとで $`\ge L(\omega+1)`$ で、(Q) は左端より下の届く先の知られた上からの評価からは出ない（CL、P-LOW、Q-OBST。[SHIFT-ja.md](SHIFT-ja.md) §8.1）。
      (P) には非可算のずれを越える届く先が要り、(Q) は 1 つの等最小の集合についての命題 (Q′) に弱められる（P-UNC、CPB-LOC。[SHIFT-ja.md](SHIFT-ja.md) §9.1）。
      (P) には、最初の添字の不動点の先での届く先の上からの評価と符号が要る（[SHIFT2-ja.md](SHIFT2-ja.md) §1.1）。今は順序型によるちょうどの蓋、鋭い越え方、η ずれが
      $`\theta`$ まで届く（[SHIFT2-ja.md](SHIFT2-ja.md) §2.1、§3.1、[SHIFT3-ja.md](SHIFT3-ja.md) §1.1、§2.1。予想 EXACT-PHI は偽）。さらに閉じた届く先（$`\delta_1\cdot\omega`$ より先の文字どおりの規則 TOP-REG は偽で、直した形を証明した）により、$`\varphi(\omega, G(\omega+1)+1)`$ までの
      ちょうどの蓋、$`D \lt G_2`$ の長いやり直し、$`\psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$ より下の η ずれ、$`G(\Omega_3+1)`$ より下の符号に届き（[SHIFT4-ja.md](SHIFT4-ja.md) §1.1、§1.4）、さらに $`G_2`$ より下のちょうどの届く先（GAP$`_j`$、ROOT-CL）と $`G(\hat\zeta_2)`$ より下の符号に届き（[SHIFT4-ja.md](SHIFT4-ja.md) §2.1、§2.2）、さらに着地の蓋（行き先を最後の前置きのやり直しの区域に置く蓋は $`\theta_3\cdot\omega^2`$ で偽）と $`D \lt \varepsilon_{G_2+1}`$ での長いやり直しのちょうどの届く先で $`G(\hat\zeta_\varepsilon)`$ より下の符号に届き（[SHIFT5-ja.md](SHIFT5-ja.md) §1.1）、さらに最初の添字の不動点までの長いちょうどの届く先と包の蓋（着地の蓋はもっと上で偽）で $`G(\hat\zeta_H)`$ より下の符号に届き（[SHIFT5-ja.md](SHIFT5-ja.md) §2.1）、さらに包の要らない蓋で $`G(\theta_4\cdot\omega^2)`$ より下の符号と $`G(\hat\zeta_{23})`$ より下の符号に届き（[SHIFT6-ja.md](SHIFT6-ja.md) §1.1、§2.1 と、そこの §3.1 の直し）、族 $`[G(\hat\zeta_3), G(\hat\zeta_3+\Omega_2))`$ と $`G(\hat\zeta_G)`$ からの $`\varepsilon`$ の層でのちょうどの着地の届く先が分かり（[SHIFT6-ja.md](SHIFT6-ja.md) §2.1、§2.2、§3.1）、$`P'`$ より下のすべての符号の届く先の下からの評価が分かった（[SHIFT6-ja.md](SHIFT6-ja.md) §3.2）。さらにどの深さでも相対的な遠いピンで、段 1 と段 2 で $`P'`$ より下のどの符号でもちょうどの届く先と蓋が分かった（[SHIFT7-ja.md](SHIFT7-ja.md) §1.1）。そのあと $`(L(\omega), L(\omega+1))`$ での
      (P)、(Q)、(Q′) は、符号 $`P'`$ での極限の越え方（CROSS-LIM）と PAIR から出た（[SHIFT7-ja.md](SHIFT7-ja.md) §2.1）
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
      — 未解決、難しい（STEP の写像 $`B`$ が、$`\Omega_\omega`$ より下で片向きにこれをする。$`\Omega_1`$ の段では、$`\Omega_1^2 + \Omega_1`$ より下の Wilken の段は
      Veblen 関数と $`\Gamma`$、VEB-THETA と GAM-THETA、[VEBLEN-ja.md](VEBLEN-ja.md) §1。Wilken の系と Weiermann–Wilken の同時に定めた系はパラメータが同じ、PAR-SAME。
      LOW-STEP の写像 $`E`$ と STEP の写像 $`B`$ は基 $`\psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$ で働く、[THETA-ja.md](THETA-ja.md) §1、§9.1）
    - A2 上限までの $`R_2^+`$ の $`\le_1`$、$`\le_2`$ の構造定理（Wilken 2021, Thm 4.2 の類似）。
      [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の結果は、$`\upsilon_{\omega^3}`$ より下でのこの定理。定理 BLK$`^O`$ が
      正確な届く先とともに $`\Lambda_\varepsilon`$ まで、定理 EXACT-A が $`\Theta_A`$ まで延ばし（[PINS-ja.md](PINS-ja.md)）、STRUCT′ が $`\rho_{\Lambda'+\omega^2}`$ まで名前で書き（[FANFREE-ja.md](FANFREE-ja.md) §10.4）、STRUCT″ が $`\rho_{\Lambda_{\mathrm{fp}2}+\omega^2}`$ まで（[VEBLEN-ja.md](VEBLEN-ja.md) §8）、KV-NAMES が
      $`\nu_C`$ より下の Klammer の届く先を名前から読み（同じ所）、$`\Theta_A`$ での値と
      目印 $`\Theta_\delta`$、$`\Theta_{d\omega}`$（[BREAK-ja.md](BREAK-ja.md) §4）とその名前、$`\Lambda^*`$ と $`\nu_P`$ の名前（[THETA-ja.md](THETA-ja.md) §9.1）、可算の指数のやり直しと $`\Lambda^*`$ の正確な届く先（EXACT-C、LONG-G2）、指数が非可算のときの最初のちょうどの届く先とすべての長いやり直しの下からの評価（EXACT-W、LONG-ALL、RL-UP。[SHIFT-ja.md](SHIFT-ja.md) §9.1）、区域を越える届く先の下からの評価（CROSS、RL-UNC、RL-2。[SHIFT2-ja.md](SHIFT2-ja.md) §1.1）、指数が $`\psi_{\Omega_2}(\Omega_2)`$ より下の短いやり直しのちょうどの届く先と、添字の不動点での鋭い越え方（EXACT-V、CROSS-SHARP。[SHIFT2-ja.md](SHIFT2-ja.md) §2.1）、長いやり直しの届く先の正確な尾 $`\delta\cdot 2 + t`$（TAIL-MIN、BASE0-TAIL。[SHIFT-ja.md](SHIFT-ja.md) §8.1、§8.4）、定理 SKEL が $`R_2^S`$ で $`[0, \nu_P)`$ で与え（[REACHES-ja.md](REACHES-ja.md)）、
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
    - A6 どこでも $`R_2^S = R_2^C`$ — 未解決（$`\beta_0 \gt \upsilon_{\omega\cdot\omega}`$ より下では一致）。その最初の場合 $`\nu_C = \nu_S`$ — FRAG のもとで証明済みで、幽霊の組は無い
      （NU。[SHIFT7-ja.md](SHIFT7-ja.md) §2.1。査読 1 回）。前の道：$`\nu_C = \nu_S`$ は 1 つの $`\Sigma_2`$ の
      命題（EQ）で、最初のブロックで証明済みの区間の条件 SC から出る（[COVER-ja.md](COVER-ja.md) §6.3）。SC は各区間の最初の部分で
      概略の水準で成り立ち（[FANFREE-ja.md](FANFREE-ja.md) §3）、今は臨界な添字の最初の極限より下（[FANFREE-ja.md](FANFREE-ja.md) §7.3）と、より大きい部分（[FANFREE-ja.md](FANFREE-ja.md) §10.3）で証明済み。
      残り：帰着がいつも要る、長いやり直しの点での SC。$`\Sigma_2`$ の形で直接扱うと、写しより上のどの拡張も合わせられる（TOP、[VEBLEN-ja.md](VEBLEN-ja.md) §4）。
      そこでの残り：写しより下の有限集合を止めたままの、局所的な基の取り替えと平行移動。局所的な部分は未解決の条件 (HC) のもとで基の
      取り替えの区域で成り立つが、そこでは平行移動が成り立たない（[VEBLEN-ja.md](VEBLEN-ja.md) §11）。今は (HC) が証明され、帰着が直され、
      「ねじれた三つ組」以外はすべて合わせられる（[THETA-ja.md](THETA-ja.md) §4）。小さい閉じた形の骨組みには、いくつものブロックを一度に含めて、ねじれた写しがある
      （[THETA-ja.md](THETA-ja.md) §9.4）。どの記号でも (PROF) が成り立ち、閉じた届く先の層がもう 1 つ分かり、1 つの具体的な性質が幽霊になるのは、長いやり直しの届く先の尾が
      $`x`$ とその下の段 2 の点で食い違うときに限る（[SHIFT-ja.md](SHIFT-ja.md) §4）。今はこの尾は食い違わない：LT は $`x`$ と段 2 のどの点でも成り立つので、
      その性質は幽霊ではない（[SHIFT-ja.md](SHIFT-ja.md) §8.4）。今は CAND-2 の判定も幽霊ではなく、予想 U-TAIL は定理で、蓋は長い写しの置き場所 (W) を
      止めず、止めうるのは場所だけ（[SHIFT-ja.md](SHIFT-ja.md) §9.4）。今は写しの計画に錨の写しが要らないので、天井の下の場所は障害でなく、遠い頭には
      場所がある（RE-PLACE、DOUBLE-FAR。[SHIFT2-ja.md](SHIFT2-ja.md) §1.4）。今は最初の添字の不動点より下のまたぎはどれもちょうど置ける
      （MIN-EXACT、SPAN-PLACE、RES-ALL\*。[SHIFT2-ja.md](SHIFT2-ja.md) §2.4）。残り：ずれが非可算の深いまたぎ (D1b) と、$`[x^\#, \nu)`$ と交わる集合。Carlson–Wilken 2012 の逆からはこれらは出ず（[SHIFT2-ja.md](SHIFT2-ja.md) §3.4）、今の道具は未解決の仮定 LOW のもとでしかそこに届かない（[SHIFT3-ja.md](SHIFT3-ja.md) §1.4）。その仮定は今は $`\nu_C \lt \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ に弱まり、
      LOW そのものは自分を越えるやり直しの蓋に帰着した（[SHIFT3-ja.md](SHIFT3-ja.md) §2.4）。その蓋は今は $`P'`$ より下のどの符号でも
      成り立ち、だから **FRAG のもとで LOW は偽**（[SHIFT7-ja.md](SHIFT7-ja.md) §1.1、査読 1 回。前は最初の試しの例と $`G(\hat\zeta_{23})`$ より下のどの符号で、[SHIFT5-ja.md](SHIFT5-ja.md) §1.1、§2.1、[SHIFT6-ja.md](SHIFT6-ja.md) §1.1、§2.1、§3.1。LOW の否定の $`P'`$ より下の EX$`^w`$ への帰着は [SHIFT6-ja.md](SHIFT6-ja.md) §2.1）。届く先は今は段 1 で符号 $`G_2^2`$ より下で基の取りかえと入れ替えられ、ずれが $`\omega^{G_2^2}`$ より下の深いまたぎは LOW のもとでは置けるが、弱い仮定のもとでは置けない（進行を止める点、[SHIFT5-ja.md](SHIFT5-ja.md) §1.2）。今は道具と $`G_2^2`$ より下の TC⁺ がどの段でも成り立つので、弱い仮定は $`\nu_C \lt \upsilon^\infty`$ になるが、原子が動く長い前置きのピンは書かれていない（進行を止める点、[SHIFT5-ja.md](SHIFT5-ja.md) §2.2）。今はそのピンは証明済みで、届く先はどの段でも符号 $`\varepsilon_{\hat G+1}`$ より下で基の取りかえと入れ替えられる。残り：LOW$`^\infty`$、もっと大きい符号でのちょうどの着地の届く先と蓋、もっと広い区域（[SHIFT6-ja.md](SHIFT6-ja.md) §1.2。今は直した進行を止める点の符号でも TC⁺ が成り立ち、$`\nu_C = \nu_S`$ は FRAG、LOW$`^\infty`$ と、$`G(\hat\zeta_{23})`$ 以上の符号でのちょうどの届く先、蓋、区域から出る、REDUCTION$`^{(6)}`$、[SHIFT7-ja.md](SHIFT7-ja.md) §1.2。さらに FRAG、LOW$`^\infty`$ と $`P'`$ 以上の符号での 2 つのものから出る、REDUCTION$`^{(7)}`$、そこの §2.2。NU がこれらの帰着を置き換え、FRAG のもとで LOW$`^\infty`$ は真、そこの §2.1）
    - A7 $`R_1^+`$ の相対化したパターンと、順序数とパターンの間の一様な対応（Wilken が予告） — 証明済み（RC-PIN、RC、U、
      UNIF。[PINS-ja.md](PINS-ja.md) §1。閉包は有限（CL-FIN）で、具体的なピンのパターン（EXPL）、[BREAK-ja.md](BREAK-ja.md) §4）。
      対応が初等再帰的であること — 概略だけ
  - **L** 下界 $`\psi_{\Omega_1}(I_\omega) \subseteq \mathrm{Core}(R_2^+)`$ — 未解決
    - L0 $`R_2^C`$ では「どの $`\gamma \lt \psi_{\Omega_1}(I_\omega)`$ も、ある $`\max C^*_n`$ より下」と同値 — 証明済み
    - L-CERT $`\theta_0`$ より下：帰着は証明済み（I-FREE、OE、EPS-RED、FS-OE、RED-BMS、S-RED、MU-A、MU-B、UNIF-V）。
      MU-0 と MU-B0 も（段 0 の (M4)。核には何も足さない）。残り：段 1 以上の (M4)、(M1)–(M3)、SRO 未満での局所的な段
      — 未解決（これらがあれば最初の扇に到達不能基数が要る、RED-HM、[COVER-ja.md](COVER-ja.md) §5.3）。SRO でのいちばん上の段と、いくつかの
      一様な段の族 — 具体的なパターンについて証明済み（[COVER-ja.md](COVER-ja.md) §6.1）。$`V_3`$ より上の標本の決まらない
      26 個の極限の跳び — 証明済み（[FANFREE-ja.md](FANFREE-ja.md) §1）。SRO より下の標本の 3,166 個すべて（IDX-ADD を含む）での、すべての $`n`$ での段と、プログラムの性質 (REP) — 証明済み（[FANFREE-ja.md](FANFREE-ja.md) §7.1、§10.1、[VEBLEN-ja.md](VEBLEN-ja.md) §3、§10、[THETA-ja.md](THETA-ja.md) §3、§9.3、[SHIFT-ja.md](SHIFT-ja.md) §3、§8.3、§9.3、[SHIFT2-ja.md](SHIFT2-ja.md) §1.3、§2.3、§3.3、[SHIFT3-ja.md](SHIFT3-ja.md) §1.3、§2.3、[SHIFT4-ja.md](SHIFT4-ja.md) §1.3、§2.3）。Bachmann–Howard
      順序数までの素の符号、そして $`\upsilon_1`$ より下のすべての添字と 1 段の参照での、さらに（ここから $`Z_\omega`$ までのどの評価 $`b`$ も $`\iota(\mathrm{CH}_2) \ge b`$ を与える）入れ子の参照と最初のブロックで $`\Phi_1`$ より下での、さらに $`\upsilon`$ の不動点のための部品で $`\Lambda_\Gamma`$ より下での、さらに入れ子の部品と飾りの付いた部品で $`\Lambda_T`$ より下での（MODULE-RED⁺、CHAIN⁺、IDX-T）、さらに枠としての入れ子の段で $`Z_K`$ より下での（CHAIN-K、IDX-K）、さらに絶対的な符号で $`Z_\Xi`$ より下での（HOST-Γ、IDX-R）、さらに $`\Omega_1`$ の上のつぶす階層と $`\le_1`$ の原子の上の入れ子で $`\theta_{\Xi_2}(0)`$ より下での素の符号（UPPER-HOST、IDX-U）、さらに $`\le_1`$ の項目の平らな 1 列と原子のブロックで $`Z^+`$ より下での素の符号（ROW2、IDX-3）、さらにどの段にも入れ子の列を置いて $`Z_\omega`$ より下での素の符号（ROW$`_j`$、IDX-n）、さらに $`\mathrm{CH}_3`$ について配置 L1p を 1 つ持つてっぺん（$`\iota(\mathrm{CH}_3) \ge Z''_\omega`$、HOST$`_k`$、IDX-ω⁺。RED-TOWER により鎖の数は行き先とともに増やしてよい）、さらに $`\omega^\omega`$ より下の段階のための組のブロック（$`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$、IDX$`^p`$）、さらに $`\upsilon^*`$ の先（$`\iota(\mathrm{CH}_3) \ge Z''_\omega \gt \upsilon^*`$、EN=EX、EMB）、さらに $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ の先（$`\iota(\mathrm{CH}_3) \ge Z[0]`$、PSI$`^T`$、EN=EX$`^T`$） — 証明済み（[FANFREE-ja.md](FANFREE-ja.md) §10.2、[VEBLEN-ja.md](VEBLEN-ja.md) §2、§9、[THETA-ja.md](THETA-ja.md) §2、§9.2、[SHIFT-ja.md](SHIFT-ja.md) §2、§8.2、§9.2、[SHIFT2-ja.md](SHIFT2-ja.md) §1.2、§2.2、§3.2、[SHIFT3-ja.md](SHIFT3-ja.md) §1.2、§2.2、[SHIFT4-ja.md](SHIFT4-ja.md) §1.2、§2.4）。さらに $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega^\omega)`$ まで（$`\iota(\mathrm{CH}_3) \ge \theta_{\Xi[\omega]}(0)`$、GEN-ALL。[SHIFT5-ja.md](SHIFT5-ja.md) §1.3）。さらに段階の区域として飾りを使い $`\psi_{\Omega_1}(\Omega_\omega\cdot\varepsilon_0)`$ まで（SUPPLY-0、DEC-REGION、PUSH$`^{\varepsilon_0}`$。[SHIFT5-ja.md](SHIFT5-ja.md) §2.3）。さらに下の符号をまるごと段階の札に使い $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_1)`$ まで（STAGE-TOWER、LADDER。[SHIFT6-ja.md](SHIFT6-ja.md) §1.3）。ただし札のブロックの系では $`\Omega_1`$ の段の段階の札は何も足さない（SIGMA-BARRIER。[SHIFT6-ja.md](SHIFT6-ja.md) §2.3）。さらに札を符号の組の中の点にして、1 つの鎖の数 3 で $`\psi_{\Omega_1}(\Omega_\omega\cdot\Omega_2)`$ まで（PAIR-DOWN、IDX$`^q`$。[SHIFT6-ja.md](SHIFT6-ja.md) §3.3）。さらにどの有限の段の段階の札と ω の上端の始まりで $`\psi_{\Omega_1}(\Omega_\omega^2\cdot\omega^\omega)`$ まで（どの順序数でも MIN-A0、査読 2 回。[SHIFT7-ja.md](SHIFT7-ja.md) §1.3、§2.3）。さらに 1 つの鎖の数 3 と札の飾りの区域で $`\psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ まで（REGION$`^L`$、SUP$`^L`$、MAJ。[SHIFT7-ja.md](SHIFT7-ja.md) §2.3）。
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
被覆に対する最小性による結果と段 0 の記述（5 回目から 7 回目）は 6 ページ目 [COVER-ja.md](COVER-ja.md) に、8 回目から 10 回目は 7 ページ目 [FANFREE-ja.md](FANFREE-ja.md)、11 回目と 12 回目は 8 ページ目 [VEBLEN-ja.md](VEBLEN-ja.md) に、13 回目と 14 回目は 9 ページ目 [THETA-ja.md](THETA-ja.md) にある（そこには、前の回のまとめと、$`R_2^S`$ と $`R_2^C`$ を比べた結果も、このページから移した）。15 回目から 17 回目は 10 ページ目 [SHIFT-ja.md](SHIFT-ja.md) に、18 回目から 20 回目は 11 ページ目 [SHIFT2-ja.md](SHIFT2-ja.md) に、21 回目と 22 回目は 12 ページ目 [SHIFT3-ja.md](SHIFT3-ja.md) に、23 回目と 24 回目は 13 ページ目 [SHIFT4-ja.md](SHIFT4-ja.md) に、25 回目と 26 回目は 14 ページ目 [SHIFT5-ja.md](SHIFT5-ja.md) に、27 回目から 29 回目は 15 ページ目 [SHIFT6-ja.md](SHIFT6-ja.md) に、30 回目と 31 回目は 16 ページ目 [SHIFT7-ja.md](SHIFT7-ja.md) にある。1 回目の結果の一部は [ROUND1-ja.md](ROUND1-ja.md) に、このページから移した古い細部は [ROUND2-ja.md](ROUND2-ja.md) にある。

## 8. 文献

- T. J. Carlson, "Elementary patterns of resemblance", APAL 108 (2001).
- T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009).
- T. J. Carlson, G. Wilken, "Normal forms for elementary patterns", JSL 77 (2012).
- T. J. Carlson, G. Wilken, "Tracking chains of Σ₂-elementarity", APAL 163 (2012), https://www.sciencedirect.com/science/article/pii/S0168007211001199.
- G. Wilken, "Pure patterns of order 2", https://arxiv.org/abs/1608.08421.
- G. Wilken, "Tracking chains revisited", https://arxiv.org/abs/1611.04348.
- G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
- G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
- A. Weiermann, G. Wilken, "Ordinal arithmetic with simultaneously defined θ-functions", MLQ 57 (2011).
- G. Wilken, "A glimpse of Σ₃-elementarity" (2020).
- G. Wilken, "Pure Σ₂-elementarity beyond the core", APAL 172 (2021).
- W. Buchholz, "A new system of proof-theoretic ordinal functions", APAL 32 (1986).
- W. Buchholz, "A simplified version of local predicativity" (1992).
- W. Pohlers, "Subsystems of set theory and second order number theory", Handbook of Proof Theory (1998), Ch. IV.
