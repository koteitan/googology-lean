[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/PoR/InaccPsi: $`R_2^+`$ の核についての Wilken の主張

パターン → [InaccPsi](../../../Notation/InaccPsi/README-ja.md)（$`\omega`$ 個の弱到達不能基数の上の
Buchholz の $`\psi`$）の項。このディレクトリには、G. Wilken の主張についての作業を置く。主張が何を言うか、
何が証明済みか、何が未解決か、そして実験。

状態の言葉：**Lean**（Lean で検査済み。`sorry` なし。公理は `propext`、`Classical.choice`、`Quot.sound`
だけ）。**証明済み**（紙の上。独立した査読者が、致命的な点も止める点も無く証明済みと判定）。**引用**
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

どちらの半分も**未解決**。

## 3. 証明済みのこと

**Lean**（このディレクトリの 3 つのファイル。ライブラリと一緒にビルドした）：

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

**紙の上で証明し、査読済み：**

- **定理 CORE-C。** $`\upsilon_{\omega\cdot\omega}`$ 未満の順序数はどれも $`\mathrm{Core}(R_2^C)`$ に入る。証明：定理 EQB の
  上限により、$`\alpha \lt \upsilon_{\omega\cdot\omega}`$ はどれも、上のすべてに $`\le_1`$ ではない。Carlson 2009,
  Thm 14.14 により、核はそういう最小の順序数（または Ord 全体）。
- **補題 RESTR。** $`\Omega_\omega`$ より下では、InaccPsi の包と、到達不能基数 1 個の Pohlers の系（Pohlers,
  "Subsystems of set theory and second order number theory", Handbook of Proof Theory 1998,
  Def 3.4.4.1）の包は一致し、$`\psi_{\Omega_{n+1}}`$ も一致する。引用した $`\mathrm{ID}_{\lt\omega}`$ の順序数
  （Wilken 2021, §1。Pohlers 1998, Fig. 1）と合わせて $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$
  （引用、間接）。文献の中に弱い所が 2 つある：Pohlers は再帰的正則順序数を正則基数に置き換えることを証明なしに
  行う。Wilken は $`\mathrm{ID}_{\lt\omega}`$ の順序数を証明なしに述べる。
- $`\psi_{\Omega_1}(0) = \Gamma_0`$、$`\vartheta_0(\varepsilon_{\Omega+1}) = \psi_{\Omega_1}(\varepsilon_{\Omega_1+1})`$（引用 + RESTR）。
- **定理 MAIN。** 次は同値：(i) $`\upsilon_{\omega\cdot\omega}`$ 未満の $`\mathrm{Core}(R_2^C)`$ の順序数はどれも可算な
  InaccPsi の項の値。(ii) $`\upsilon_{\omega\cdot\omega}`$ 未満の順序数はどれもそう。(iii) **予想 U**：
  $`\upsilon_{\omega\cdot\omega} \le D`$。ここで $`D = \sup_a \psi_{\Omega_1}(a)`$。証明：CORE-C と補題 IS。
- **定理 CC**（$`R_2^C`$ で）。$`C^*_n`$ を、互いに $`\le_2`$ な $`n`$ 個の加法的主要数の集合のうち、各点ごとに最小の
  ものとする。すると $`\mathrm{Core}(R_2^C) = \sup_n \max C^*_n`$。加法的主要数を $`n`$ 個持つパターンの最小の実現は
  $`\max C^*_{n+1}`$ より下。だから $`R_2^C`$ では、主張は最小の $`\le_2`$ 鎖についての命題になる。（Wilken の
  $`R_2^S`$ ではまだ言えない。）
- 小さな補題：**PRINC**（$`x \lt_1 y`$ なら $`x`$ は加法的主要数。$`x \lt_2 y`$ なら $`y`$ は加法的主要数）、
  **ISO-UNION**（isominimal な集合の有限個の合併は isominimal）、**HULL**（非可算な正則基数 $`\kappa`$ は、上の
  すべてに $`\le_1`$。両方の構造で）、**CORE-S**（$`R_2^S`$ でも同じ核の結果。未解決の葉 2 つを仮定）、
  **DOM₁**（$`\lt_2`$ の組を持たないパターンの最小の実現は $`\upsilon_1`$ より下）。
- $`C^*_2 = \{\upsilon_\omega, \upsilon_{\omega+1}\}`$。[R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の補題 FRAG
  （そこでは見取り図としてだけ認められた）を仮定すれば $`\min C^*_3 \ge \upsilon_{\omega^3}`$。

**証明されていないこと：**

- **$`\upsilon_{\omega\cdot\omega}`$ より下での主張。** 予想 U で止まっている。証明済みは $`\upsilon_1`$ より下だけ
  （引用した $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ と補題 IS）。
- 極限の段（補題 CONT）により、予想 U は後者の段から出る：$`\upsilon_\xi = \psi_{\Omega_1}(A)`$ なら
  $`\upsilon_{\xi+1} \le \psi_{\Omega_1}(A + \theta)`$。見つけたどの道も、Wilken の $`\vartheta`$ の項を InaccPsi の包へ
  埋め込むことを要する。Weiermann–Wilken 2011, 117 ページは、そういう翻訳を今後の研究に残している。
- $`\upsilon_{\omega\cdot\omega}`$ より下の $`\mathrm{Core}(R_2^S)`$：分かっているのは、定理 S
  （[R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md)）のパターンの点が入ることだけ。
- 道筋の査読者は、止める穴を 1 つ見つけた：鎖への帰着（定理 CC）とすべての証明書は $`R_2^C`$ についてのもので、
  Wilken の主張は $`R_2^S`$ についてのもの。移すには $`R_2^S = R_2^C`$ が要り、これは未解決。

## 4. Wilken の点の名前（予想 T）

**予想 T。** $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$ として、$`\eta \le \omega^2`$ で：

```math
\upsilon_{1+\eta} = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta).
```

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
大きすぎる（Lean：$`u(\omega^2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$）。$`+\theta`$ の理由：Wilken の $`T^\tau`$ では、
$`\Omega_1`$ の段の部分の上限は、どの基 $`\tau`$ でも同じ $`\vartheta_1`$。InaccPsi では $`\theta`$ がその役をする
（発見的）。根拠：[R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の翻訳 `por/tr3.py` は、定理 S の行列でこれらの点を
与える（確認済み）。予想 T から予想 U が出る。

## 5. 道筋：補題の木

道は 3 つ：B は上界、A は全部の解析、L は下界。以下で「長さ $`n`$ の鎖」は、互いに $`\le_2`$ な
$`n`$ 個の加法的主要数のこと。

- **W** Wilken の主張、$`\mathrm{Core}(R_2^+) = \psi_{\Omega_1}(I_\omega)`$ — 未解決
  - **Low** $`\upsilon_{\omega\cdot\omega}`$ より下
    - 予想 U。後者の段 $`\upsilon_{\xi+1} \le \psi_{\Omega_1}(A + \theta)`$ から — 未解決
      （$`\vartheta \to \psi`$ の埋め込みが要る。Weiermann–Wilken 2011 の同時に定義した $`\bar\vartheta`$ から始める）
    - 予想 T（§4 の名前） — 予想
    - $`\mathrm{Core}(R_2^S)`$ が $`\upsilon_{\omega\cdot\omega}`$ 全体を含む — 未解決（$`R_2^S`$ での Carlson 2009,
      Thm 14.10「極小な写しは最小の写し」が要る）
  - **B** 上界 $`\mathrm{Core}(R_2^+) \subseteq \psi_{\Omega_1}(I_\omega)`$ — 未解決
    - B0 最小の鎖への帰着（定理 CC） — $`R_2^C`$ で証明済み
      - B0-S $`R_2^S`$ で同じこと — 未解決
        - $`R_2^S`$ の関係はどれも $`R_2^C`$ の関係（Wilken 2021, Lemma 1.7 と、定理 EQ の先頭の項への置き換えから）
          — 未解決、中くらい
        - 被覆から同型な写しを作る。または $`R_2^S`$ で「isominimal な実現は、どの閉じた被覆よりも各点で下」
          — 未解決、難しい
    - B1 どの長さ $`n`$ でも、$`\psi_{\Omega_1}(I_\omega)`$ より下の鎖を InaccPsi の値で具体的に書く — 未解決、研究
      （$`n = 3`$ の候補も無い）
    - B2 $`\lt_2`$ の有限集合による判定（Wilken 2021, Prop 1.6 は + の無い $`R_2`$ のもの。+ への移行は未確認）
      — 未解決、易しい
    - B3 $`0, +, \le, \le_1, \le_2`$ を保つ基の付け替え（補題 FRAG を $`\le_2`$ に広げる）。B4 と一緒に証明する
      — 未解決、とても難しい
    - B4 B3 が動かす点の間の $`\le_2`$ の組 — 未解決、とても難しい
    - B5 B2 + B3 + B4 を組み立てる — 形だけ
    - B-PT 証明論の別の道：到達不能基数 $`n`$ 個の理論が「長さ $`n`$ の鎖がある」を証明する — 未解決。
      $`\lt_2`$ の集合論的な十分条件が要るが、知られていない
  - **A** 全部の解析 — 未解決
    - A1 どの基の上でも、すべての $`\Omega_\xi`$ と $`I_n`$ のつぶす関数を同時に定義した包の系を作り、InaccPsi と比べる
      — 未解決、難しい
    - A2 上限までの $`R_2^+`$ の $`\le_1`$、$`\le_2`$ の構造定理（Wilken 2021, Thm 4.2 の類似）。
      [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の結果は、$`\upsilon_{\omega^3}`$ より下でのこの定理 — 未解決、
      とても難しい
    - A3 最小の実現を項で書く — 未解決
    - A4 **予想 CH**：長さ $`k+2`$ の最小の鎖には到達不能基数が $`k`$ 個要る — 予想
    - A5 上限より下のどの項も、あるパターンの値 — 未解決
    - A6 どこでも $`R_2^S = R_2^C`$ — 未解決
  - **L** 下界 $`\psi_{\Omega_1}(I_\omega) \subseteq \mathrm{Core}(R_2^+)`$ — 未解決
    - L0 $`R_2^C`$ では「どの $`\gamma \lt \psi_{\Omega_1}(I_\omega)`$ も、ある $`\max C^*_n`$ より下」と同値 — 証明済み
    - L-CERT InaccPsi の項からパターンへの順序を保つ埋め込みで、各段を Carlson の規則の証明書で確かめるもの
      （$`R_2^+`$ の値は要らない）。まず $`\psi_{\Omega_1}(I_0)`$ より下の項で — 未解決、一番やりやすい
    - L-BMS $`\Phi_3`$ を通す道 — 止まっている：調べた $`\Phi_3`$ のパターンは長さ 2 の鎖しか持たない（§6）
  - **わきの葉**
    - **DOM₂**：長さ 3 の鎖を持たないパターンは $`\min C^*_3`$ より下 — 証明書 8 個で確認済み
    - $`C^*_3`$ の場所を見つける — 未解決（分かっていること：FRAG を仮定すれば $`\min C^*_3 \ge \upsilon_{\omega^3}`$）
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

**最初の到達不能基数。** 大きさ 9 以下の標準形 1,650,729 個をすべて並べた：$`I`$ の記号を含む最小の可算な項は
$`\psi_{\Omega_1}(\psi_{I_0}(0))`$ で、$`I`$ の記号を含まない可算な項はすべてそれより下（確認済み）。予想：$`I_0`$ が
要る最初のパターンは $`\Phi_3(\mathrm{SRO})`$（$`\mathrm{SRO} = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)`$）で、その点は
$`\psi_{\Omega_1}(\psi_{I_0}(0))`$。根拠：$`\mathrm{SRO}[n]`$ は高さ $`n+2`$ の $`\Omega`$ の塔の $`\psi_{\Omega_1}`$ と読める。
証明書で $`n = 2, 3`$ の $`\Phi_3(\mathrm{SRO}[n]) \lt \Phi_3(\mathrm{SRO})`$。$`n = 4`$ は時間切れ。$`I_1`$ が最初に要る場所は
未解決。

**鎖と $`\Phi_3`$。** $`V_3`$ から $`(0,0,0)(1,1,1)(2,2,2)(3,3,0)`$ までの 14 個の行列で、パターン $`\Phi_3(M)`$ の
$`\le_2`$ 鎖の長さは 2 以下（確認済み）。証明書は、そのうち 8 個で $`\Phi_3(M)`$ の点を $`\min C^*_3`$ より下に、
9 個で $`\max C^*_3`$ より下に置く。予想 CH が正しければ、順序を保つ $`\Phi_3`$ は、最初の到達不能基数を越えたら
長さ 3 以上の鎖を使わなければならない。長さ 2 の鎖だけでは $`\psi_{\Omega_1}(I_\omega)`$ に届かない。この帰結は
**証明されていない**：証明されていない行列の値が要り、しかも $`R_2^C`$ だけの話である。

## 7. ファイル

| ファイル | 何を証明するか |
|---|---|
| [CountSeg.lean](CountSeg.lean) | 補題 L、`bounded_inter_Om1`、`vals_inter_Om1`、`three_bounds` |
| [LowSeg.lean](LowSeg.lean) | 補題 IS と補題 CONT |
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
