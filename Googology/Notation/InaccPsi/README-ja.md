[← 戻る](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# InaccPsi: 最初の $`\omega`$ 個の弱到達不能基数の上の Buchholz の $`\psi`$

このディレクトリは、$`\omega`$ 個の弱到達不能基数 $`I_0 \lt I_1 \lt \cdots`$ とその上限 $`I_\omega`$ の上の
順序数崩壊関数を定義する。その表記系も定義する。

- **土台。** 弱到達不能基数 1 つ $`I`$ の上の崩壊関数は、W. Buchholz,
  *A simplified version of local predicativity*
  (in P. Aczel, H. Simmons, S. S. Wainer (eds.), *Proof Theory*, Cambridge University
  Press 1992, 115–147) の定義 4.2 である。W. Pohlers, *Subsystems of set theory and second order number
  theory* (Handbook of Proof Theory, Elsevier 1998, Chapter IV) の §3.4.4 も、
  同じ定義を載せている。そこには事実 (155)–(179) と項の体系の概略もある。
- **拡張。** $`\omega`$ 個の弱到達不能基数への拡張は、ここで新しく作ったものである（koteitan
  と Claude）。G. Wilken, *A glimpse of Σ₃-elementarity* (2020) の p. 421 は、
  「最初の $`\omega`$ 個の弱到達不能基数から得られる Skolem 包の表記系」が $`R_2^+`$ の核を覆う、と
  主張している。ただし定義は書いていない。ここの体系は、その言い方を正確にする
  1 つの方法である。これが Wilken の考えていた体系と同じだという根拠は無い。

## 1. 仮定と記法

- $`\Omega_0 = 0`$ とする。$`\xi \ge 1`$ では $`\Omega_\xi = \omega_\xi`$（$`\aleph_\xi`$ に当たる順序数）とする。よって $`\xi \mapsto \Omega_\xi`$ は
  $`\{0\}`$ と非可算基数を順に並べる。これは狭義単調増加で、連続である。
- $`\varphi (\xi, \eta)`$ は 2 変数の Veblen 関数で、$`\varphi (0, \eta) = \omega^\eta`$ である。$`1 = \varphi (0, 0)`$ である。
- $`\mathrm{SC}`$ は強臨界順序数のクラスである。つまり $`\gamma \gt 0`$ で、全ての $`\xi, \eta \lt \gamma`$ について
  $`\varphi (\xi, \eta) \lt \gamma`$ となるものである。非可算基数はどれも $`\mathrm{SC}`$ に入る。
- **仮定。** $`I : \mathbb{N} \to \mathrm{Ord}`$ は狭義単調増加である。どの $`I_n`$ も非可算正則基数で、
  $`\Omega_{I_n} = I_n`$ を満たす（弱到達不能基数である）。
  $`I_\omega = \sup_n I_n`$ とおく。このとき $`\Omega_{I_\omega} = I_\omega`$ も成り立つ。$`I_n`$ が
  最初の $`\omega`$ 個の弱到達不能基数であることは仮定**しない**。以下ではそれを使わないからである。
- $`R = \{I_n \mid n \lt \omega \} \cup \{\Omega_{s+1} \mid s \in \mathrm{Ord}\}`$ とおく。$`R`$ の元はどれも非可算正則基数である。
  これが $`\psi`$ が崩壊する添字である。

## 2. 定義

$`\alpha`$ についての再帰で、集合 $`\mathrm{Cl}(\alpha, \beta)`$ と順序数 $`\psi_\kappa (\alpha)`$（$`\kappa \in R`$）を定義する。

- $`\mathrm{Cl}(\alpha, \beta)`$ は次を満たす最小の集合 $`X`$ である。
  - $`\beta \subseteq X`$、$`0 \in X`$、全ての $`n \lt \omega`$ について $`I_n \in X`$、$`I_\omega \in X`$。
  - $`\xi, \eta \in X`$ $`\Rightarrow`$ $`\xi + \eta \in X`$、$`\varphi (\xi, \eta) \in X`$、$`\Omega_\xi \in X`$。
  - $`\xi, \pi \in X`$、$`\xi \lt \alpha`$、$`\pi \in R`$ $`\Rightarrow`$ $`\psi_\pi (\xi) \in X`$。
- $`\psi_\kappa (\alpha) = \min \{\beta \mid \kappa \in \mathrm{Cl}(\alpha, \beta) \land \mathrm{Cl}(\alpha, \beta) \cap \kappa \subseteq \beta \}`$。

到達不能基数が 1 つ $`I`$ のとき（$`I_n`$ が全部 $`I`$ に等しく、$`I_\omega`$ が無いとき）、これは Buchholz の
定義そのものである。変えたのは、定数 $`I_n`$、$`I_\omega`$ と、添字のクラス $`R`$ だけである。

## 3. $`\psi`$ についての事実

$`\kappa`$ は $`R`$ の元を動く。角括弧の中の番号は Pohlers のものである。

**F1（単調）。** $`\alpha \le \alpha '`$ かつ $`\beta \le \beta '`$ $`\Rightarrow`$ $`\mathrm{Cl}(\alpha, \beta) \subseteq \mathrm{Cl}(\alpha ', \beta ')`$。[155]

**F2（大きさ）。** $`\lvert \mathrm{Cl}(\alpha, \beta)\rvert \le \max(\lvert \beta \rvert, \aleph_0)`$。[157] — この集合は $`\omega`$ 個の段の
合併である。各段は、前の段に有限個の有限項演算を施し、
$`\omega + 1`$ 個の定数を加えたものである。

**F3。** ある $`\beta \lt \kappa`$ について $`\kappa \in \mathrm{Cl}(\alpha, \beta)`$。— $`\kappa = I_n`$ なら定数である。
$`\kappa = \Omega_{s+1}`$ なら $`\beta = s + 1 \lt \kappa`$ をとる。すると $`s \in \mathrm{Cl}`$、$`s + 1 = s + \varphi (0,0) \in \mathrm{Cl}`$、
$`\Omega_{s+1} \in \mathrm{Cl}`$ となる。

**F4（崩壊）。** $`\psi_\kappa (\alpha) \lt \kappa`$、$`\kappa \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$、$`\mathrm{Cl}(\alpha, \psi_\kappa (\alpha)) \cap \kappa \subseteq \psi_\kappa (\alpha)`$、
$`\psi_\kappa (\alpha) \notin \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$。[160] — F3 の $`\beta_0 \lt \kappa`$ から始め、
$`\beta_{n+1} = \sup(\mathrm{Cl}(\alpha, \beta_n) \cap \kappa)`$ とおく。F2 と $`\kappa`$ の正則性から $`\beta_{n+1} \lt \kappa`$ である。
$`\operatorname{cf} \kappa \gt \omega`$ なので $`\beta = \sup_n \beta_n \lt \kappa`$ である。$`\mathrm{Cl}(\alpha, \beta)`$ は $`\mathrm{Cl}(\alpha, \beta_n)`$ の
合併なので、この $`\beta`$ は条件を満たす。最後の主張: $`\psi_\kappa (\alpha) \in \mathrm{Cl} \cap \kappa \subseteq \psi_\kappa (\alpha)`$ は起こりえない。

**F5。** $`\alpha_0 \lt \alpha`$ かつ $`\alpha_0 \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$ $`\Rightarrow`$ $`\psi_\kappa (\alpha_0) \lt \psi_\kappa (\alpha)`$。[161] — $`\psi_\kappa (\alpha_0)`$ は
$`\mathrm{Cl}(\alpha, \psi_\kappa (\alpha)) \cap \kappa \subseteq \psi_\kappa (\alpha)`$ に入る。F4 より、それは $`\psi_\kappa (\alpha)`$ ではない。

**F6。** $`\psi_\kappa (\alpha) \in \mathrm{SC}`$。[163] — $`0 \in \mathrm{Cl} \cap \kappa`$ から $`\psi_\kappa (\alpha) \gt 0`$ である。$`\xi, \eta \lt \psi_\kappa (\alpha)`$ なら、
$`\kappa \in \mathrm{SC}`$ なので $`\varphi (\xi, \eta) \in \mathrm{Cl} \cap \kappa`$ である。

**F7（基数）。** $`\Omega_\sigma \in \mathrm{Cl}(\alpha, \beta)`$ $`\Rightarrow`$ $`\sigma \in \mathrm{Cl}(\alpha, \beta)`$。[164] — $`x \in \mathrm{Cl}(\alpha, \beta)`$ の
生成についての帰納法で示す。示すこと: $`x = \Omega_\sigma`$ なら $`\sigma \in \mathrm{Cl}(\alpha, \beta)`$。
- $`x \lt \beta`$ のとき: $`\sigma \le \Omega_\sigma \lt \beta`$。
- $`x \in \{0, I_n, I_\omega \}`$ のとき: $`\Omega`$ は単射で、これらは $`\Omega`$ の不動点である。よって $`\sigma = x`$。
- $`x = \xi + \eta`$ のとき: $`\Omega_\sigma`$ は $`0`$ か加法的主要である。よって $`\eta = \Omega_\sigma`$ か $`\eta = 0 \land \xi = \Omega_\sigma`$。
- $`x = \varphi (\xi, \eta)`$ のとき: $`\Omega_\sigma \in \mathrm{SC}`$（または $`\sigma = 0`$）である。よって $`\xi = \Omega_\sigma`$ か $`\eta = \Omega_\sigma`$。
- $`x = \Omega_\xi`$ のとき: $`\xi = \sigma`$。
- $`x = \psi_\pi (\xi)`$ のとき: $`\sigma = \Omega_\sigma`$ なら $`\sigma = x \in \mathrm{Cl}`$。そうでなければ $`\sigma \lt \Omega_\sigma = \psi_\pi (\xi) =: \gamma`$ である。よって
  $`\sigma \in \gamma \subseteq \mathrm{Cl}(\xi, \gamma)`$ で、$`\Omega_\sigma \in \mathrm{Cl}(\xi, \gamma) \cap \pi \subseteq \gamma`$、つまり $`\gamma \lt \gamma`$ となる。これは起こりえない。

**F8（後続）。** $`s + 1 \in \mathrm{Cl}(\alpha, \beta)`$ $`\Rightarrow`$ $`s \in \mathrm{Cl}(\alpha, \beta)`$。— 同じ帰納法で示す。
$`\eta \ne 0`$ で $`\xi + \eta = s + 1`$ なら、$`\eta = t + 1`$、$`s = \xi + t`$ となる。$`\varphi`$ の値で
後続のものは $`1`$ に等しい。$`\Omega`$ の値と $`\psi`$ の値は $`0`$ か極限である（F6）。

**F9（後続の添字）。** $`\kappa = \Omega_{s+1}`$ について: $`\Omega_s \lt \psi_\kappa (\alpha) \lt \Omega_{s+1}`$。よって $`\psi_\kappa (\alpha)`$
は基数ではない（$`s = 0`$ のとき: $`\psi_\kappa (\alpha)`$ は可算）。[167] — $`\kappa \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$
（F4）なので、$`s + 1`$ と $`s`$ もそこに入る（F7、F8）。$`s \lt \kappa`$ なので $`s \in \mathrm{Cl} \cap \kappa`$ で、`Ω_s ∈ Cl ∩ κ
⊆ $`\psi`$_κ(α)` となる。

**F10（到達不能基数の添字）。** $`\kappa = I_n`$ について: $`\Omega_{\psi_\kappa (\alpha)} = \psi_\kappa (\alpha)`$ である。また
$`n \ge 1`$ のとき $`I_{n-1} \lt \psi_\kappa (\alpha) \lt I_n`$ である（$`n = 0`$ のときは $`\Omega_1 \lt \psi_\kappa (\alpha)`$）。[170] — $`I_{n-1}`$
（$`n = 0`$ のときは $`\Omega_1`$）は $`\mathrm{Cl} \cap \kappa`$ に入る。不動点であることの証明: $`\gamma = \psi_\kappa (\alpha)`$ とおき、
$`\Omega_\sigma \le \gamma \lt \Omega_{\sigma +1}`$ とする。$`I_n`$ は極限基数なので $`\Omega_{\sigma +1} \lt I_n`$ である。よって
$`\Omega_{\sigma +1} \notin \mathrm{Cl}(\alpha, \gamma)`$ である（入っていれば $`\Omega_{\sigma +1} \lt \gamma`$ となる）。よって $`\sigma \notin \mathrm{Cl}(\alpha, \gamma)`$ で、$`\sigma \ge \gamma`$ である。よって
$`\Omega_\sigma \ge \sigma \ge \gamma \ge \Omega_\sigma`$ で、$`\gamma = \sigma = \Omega_\sigma`$ となる。

**F11（引数について単調）。** $`\xi \le \alpha`$ $`\Rightarrow`$ $`\psi_\kappa (\xi) \le \psi_\kappa (\alpha)`$ かつ
$`\mathrm{Cl}(\xi, \psi_\kappa (\xi)) \subseteq \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$。[168] — $`\kappa \in \mathrm{Cl}(\xi, \psi_\kappa (\alpha))`$ を示す。$`\kappa = I_n`$ なら
定数である。$`\kappa = \Omega_{s+1}`$ なら $`s \lt \Omega_s \lt \psi_\kappa (\alpha)`$（F9）である。さらに
$`\mathrm{Cl}(\xi, \psi_\kappa (\alpha)) \cap \kappa \subseteq \mathrm{Cl}(\alpha, \psi_\kappa (\alpha)) \cap \kappa \subseteq \psi_\kappa (\alpha)`$ である。

**F12（標準的な引数で狭義単調）。** $`\alpha_0 \lt \alpha`$ かつ
$`\alpha_0 \in \mathrm{Cl}(\alpha_0, \psi_\kappa (\alpha_0))`$ なら、$`\psi_\kappa (\alpha_0) \lt \psi_\kappa (\alpha)`$。— F11 より $`\alpha_0 \in \mathrm{Cl}(\alpha, \psi_\kappa (\alpha))`$ である。F5 を使う。

## 4. 項の体系

### 項

```math
t \mathrel{::=} 0 \mid I_n \mid I_\omega \mid t + t \mid \varphi(t, t) \mid \Omega_t \mid \psi^S_s(t) \mid \psi^I_n(t) \qquad (n \in \mathbb{N})
```

$`\psi^S_s(a)`$ は $`\psi_{\Omega_{s+1}}(a)`$ を表す。$`\psi^I_n(a)`$ は $`\psi_{I_n}(a)`$ を表す。項の
値 $`\lvert t\rvert`$ は、そのまま読んだ順序数である。添字は一般の項ではない。$`R`$ の添字は、
後続基数（$`s`$ で与える）か $`I_n`$（$`n`$ で与える）のどちらかである。

### 項の種類

- **SC 項**: $`I_n`$、$`I_\omega`$、$`\Omega_a`$、$`\psi^S_s(a)`$、$`\psi^I_n(a)`$。
- **主項**: SC 項と $`\varphi (a, b)`$。
- **不動点項** $`F`$: $`I_n`$、$`I_\omega`$、$`\psi^I_n(a)`$（$`\Omega_x = x`$ となる値 $`x`$）。
- **基数項** $`K`$: $`F`$ と $`\Omega_a`$。

### 標準形 $`\mathrm{NF}`$

- $`0`$、$`I_n`$、$`I_\omega`$ は $`\mathrm{NF}`$ に入る。
- $`a + b`$ が $`\mathrm{NF}`$ に入るのは、$`a`$ が主項で $`\mathrm{NF}`$ に入り、$`b \ne 0`$ が $`\mathrm{NF}`$ に入り、$`b`$ の最初の
  加数が $`\le a`$ のときである。
- $`\varphi (a, b)`$ が $`\mathrm{NF}`$ に入るのは、$`a, b \in \mathrm{NF}`$、$`a \lt \varphi (a, b)`$、$`b \lt \varphi (a, b)`$ のときである。
- $`\Omega_a`$ が $`\mathrm{NF}`$ に入るのは、$`a \in \mathrm{NF}`$、$`a \ne 0`$、$`a \notin F`$ のときである。
- $`\psi^S_s(a)`$ が $`\mathrm{NF}`$ に入るのは、$`s, a \in \mathrm{NF}`$ かつ $`K_{\psi^S_s(a)}(a) \lt a`$ のときである。
- $`\psi^I_n(a)`$ が $`\mathrm{NF}`$ に入るのは、$`a \in \mathrm{NF}`$ かつ $`K_{\psi^I_n(a)}(a) \lt a`$ のときである。

ここで $`\lt`$ は下の比較である。$`K_\mu (a) \lt a`$ は、有限集合 $`K_\mu (a)`$ の全ての元が
$`\lt a`$ であることをいう。

### 集合 $`K_\mu (a)`$

項 $`\mu`$ について、$`K_\mu (a)`$ は、$`a`$ の中の崩壊のうち $`\mu`$ より下にないものの引数を
集めた有限集合である（Pohlers の定義 3.4.4.2）。

- $`K_\mu (0) = K_\mu (I_n) = K_\mu (I_\omega) = \emptyset`$。
- $`K_\mu (a + b) = K_\mu (a) \cup K_\mu (b)`$、$`K_\mu (\varphi (a, b)) = K_\mu (a) \cup K_\mu (b)`$。
- SC 項 $`a \lt \mu`$ について: $`K_\mu (a) = \emptyset`$。
- $`a \ge \mu`$ について: $`K_\mu (\Omega_b) = K_\mu (b)`$、$`K_\mu (\psi^S_s(b)) = \{b\} \cup K_\mu (s) \cup K_\mu (b)`$、
  $`K_\mu (\psi^I_n(b)) = \{b\} \cup K_\mu (b)`$。

**健全性（Pohlers の (178) のやさしい方の半分）。** $`a \in \mathrm{NF}`$ で、
$`K_\mu (a)`$ の全ての元が $`\lt \alpha`$ なら、$`\lvert a\rvert \in \mathrm{Cl}(\alpha, \lvert \mu \rvert)`$ である。— $`a`$ についての帰納法で示す。$`K`$ の各条項は
$`\mathrm{Cl}`$ の条項に 1 つずつ対応する。もう半分は整列性には要らない。

これから、$`\psi^S_s(a) \in \mathrm{NF}`$ なら $`\lvert a\rvert \in \mathrm{Cl}(\lvert a\rvert, \psi_{\Omega_{\lvert s\rvert +1}}(\lvert a\rvert))`$ となる。
$`\psi^I_n(a) \in \mathrm{NF}`$ なら $`\lvert a\rvert \in \mathrm{Cl}(\lvert a\rvert, \psi_{I_n}(\lvert a\rvert))`$ となる。よって F12 は、標準形の崩壊の
引数に使える。どちらでも上界 $`\mu`$ は崩壊の項そのもので、これが標準形であることはまだ
分かっていない。使うのは `cmp x μ = .lt → |x| < |μ|` の向きだけである
（`lt_psiS_of_cmp`、`lt_psiI_of_cmp`）。

前の版では、$`\psi^S_s(a)`$ の上界に $`\mathrm{card}(\Omega_s)`$ を使っていた。この条件は強すぎる。
$`s = \psi^I_0(I_0)`$ のとき、$`\bigcup_a \mathrm{Cl}(a, 0)`$ の順序数 $`\psi_{\Omega_{\lvert s\rvert +1}}(\lvert s\rvert + 1)`$ に標準形が
なかった。$`K_s(s + 1) = \{I_0\}`$ で $`\lvert s\rvert + 1 \lt I_0`$ だからである。一方、自分の閉包に入る
引数 $`a`$ でこの $`\psi`$ の値を持つものは $`\lvert s\rvert + 1`$ だけである。

### 基数部分 $`\mathrm{card}(t)`$

$`\mathrm{card}(t)`$ は基数項か $`0`$ である。$`\lvert \mathrm{card}(t)\rvert`$ は $`\lvert t\rvert`$ の基数の水準
（$`\Omega_\sigma \le \lvert t\rvert`$ となる最大の $`\Omega_\sigma`$、無ければ $`0`$）である。

- $`\mathrm{card}(0) = 0`$。$`\mathrm{card}(a + b) = \mathrm{card}(a)`$。$`\mathrm{card}(\varphi (a, b)) = \max(\mathrm{card}(a), \mathrm{card}(b))`$。
- $`t \in K`$ について $`\mathrm{card}(t) = t`$。
- $`\mathrm{card}(\psi^S_s(a)) = \mathrm{card}(\Omega_s)`$。ここで $`\mathrm{card}(\Omega_s)`$ は、$`s = 0`$ なら $`0`$、$`s \in F`$ なら $`s`$、
  それ以外なら $`\Omega_s`$ を表す。

### 比較

項の上の $`a \lt b`$ は、$`\mathrm{size}(a) + \mathrm{size}(b)`$ についての再帰で定義する。

1. $`0 \lt b`$ となるのは $`b \ne 0`$ のときである。$`a \lt 0`$ にはならない。
2. 和（主項は加数 1 つの和とみなす）: 加数のリストを辞書式に比べる。
   真の前半の方が小さい。
3. $`\varphi (a, b)`$ と $`\varphi (c, d)`$: $`a \lt c \land b \lt \varphi (c, d)`$、または $`a = c \land b \lt d`$、または
   $`c \lt a \land \varphi (a, b) \lt d`$。
4. $`\varphi (a, b)`$ と SC 項 $`s`$（強臨界な $`\gamma`$ について、$`\xi \lt \gamma`$ なら $`\varphi (\xi, \gamma) = \gamma`$、また
   $`\varphi (\gamma, 0) = \gamma`$）:
   - $`a \lt s`$ のとき: $`b`$ と $`s`$ を比べる。
   - $`a = s`$ のとき: $`b = 0`$ なら $`\varphi (a, b) = s`$、そうでなければ $`\varphi (a, b) \gt s`$。
   - $`a \gt s`$ のとき: $`\varphi (a, b) \gt s`$。

   これらは順序数の等式と不等式なので、正規形でない $`\varphi (a, b)`$ についても成り立つ。
   $`\mathrm{NF}`$ の条件 $`a \lt \varphi (a, b)`$ と $`b \lt \varphi (a, b)`$ は、$`\varphi (s, 0)`$ と、$`a \lt s`$ のときの
   $`\varphi (a, s)`$ を除く。
5. SC 項どうし:
   - $`\Omega_a \lt \Omega_c`$ となるのは $`a \lt c`$ のとき。$`f \in F`$ について: $`\Omega_a \lt f`$ となるのは $`a \lt f`$ のとき、$`f \lt \Omega_a`$ となるのは
     $`f \lt a`$ のとき。
   - $`I_n \lt I_m`$ となるのは $`n \lt m`$ のとき。$`I_n \lt I_\omega`$。$`\psi^I_n(a) \lt I_m`$ となるのは $`n \le m`$ のとき。
     $`I_m \lt \psi^I_n(a)`$ となるのは $`m \lt n`$ のとき。$`\psi^I_n(a) \lt I_\omega`$。
     $`\psi^I_n(a) \lt \psi^I_m(b)`$ となるのは $`n \lt m \lor (n = m \land a \lt b)`$ のとき。
   - $`\psi^S_s(a) \lt \psi^S_t(b)`$ となるのは $`s \lt t \lor (s = t \land a \lt b)`$ のとき。
   - 基数項 $`k`$ について: $`\psi^S_s(a) \lt k`$ となるのは $`\mathrm{card}(\Omega_s) \lt k`$ のとき、$`k \lt \psi^S_s(a)`$ となるのは
     $`k \le \mathrm{card}(\Omega_s)`$ のとき。

### 主定理

$`\mathrm{NF}`$ の項の上で、$`a \lt b \iff \lvert a\rvert \lt \lvert b\rvert`$。よって $`\lvert\cdot\rvert`$ は $`\mathrm{NF}`$ の上で単射で、$`(\mathrm{NF}, \lt)`$ は
狭義の整列順序である。これは順序数の集合と順序同型である。どの `InaccSeq` についても
`Correct.lean` で証明した: `Term.cmp_eq_compare`、`Term.eq_of_val_eq`、`Term.isWellOrder_cmp`。

条項ごとに使う事実:
- 3、4: Veblen 関数（Mathlib）と F6。
- 5 の 1 行目: $`\Omega`$ が狭義単調増加であること、不動点。
- 5 の 2 行目: F10。
- 5 の 3 行目と 4 行目: F9 と F12（$`K`$ の健全性を通して）。

### 完全性

$`\mathrm{NF}`$ の項の値の集合は、ちょうど $`\bigcup_a \mathrm{Cl}(a, 0)`$ である。どの `InaccSeq` についても
`Onto.lean` で証明した（`Term.vals_eq`）。主定理と合わせると、$`\bigcup_a \mathrm{Cl}(a, 0)`$ の各元は
ちょうど 1 つの $`\mathrm{NF}`$ 項の値である（`Term.existsUnique_NF`）。

- $`\subseteq`$: 項の各条項は $`\mathrm{Cl}`$ の条項である（`Term.exists_mem_CSet`）。
- $`\supseteq`$: $`\mathrm{Cl}`$ についての帰納法。$`x + y`$ には `addNF` を使う。これは左の項の加数のうち、
  右の項の先頭より小さいものを落とす。$`\varphi (x, y)`$ は $`x`$、$`y`$、または標準形 $`\varphi (a, b)`$ である。
  $`\Omega_x`$ は $`0`$、$`x`$（$`\Omega`$ の不動点）、または $`\Omega_a`$ である。
- $`\psi_\kappa (\xi)`$ には $`\xi`$ についての帰納法を使う。$`\gamma = \psi_\kappa (\xi)`$、
  $`M(\xi) = \min(\mathrm{Cl}(\xi, \gamma) \cap [\xi, \infty))`$ とおく。引数が $`[\xi, M(\xi))`$ にある崩壊は
  $`\mathrm{Cl}(M(\xi), \gamma)`$ に入らないので、$`\mathrm{Cl}(M(\xi), \gamma) = \mathrm{Cl}(\xi, \gamma)`$ である。よって
  $`\psi_\kappa (M(\xi)) = \gamma`$ かつ $`M(\xi) \in \mathrm{Cl}(M(\xi), \psi_\kappa (M(\xi)))`$ である（`psi_M_eq`、`M_mem_self`）。
  $`M(\xi)`$ は $`\xi`$ の部分から計算する（`NFM.lean`）。$`R = \mathrm{Cl}(\xi, \gamma)`$ として:
  - 和: 先頭の加数が $`R`$ に入るならそれを残す。入らないなら $`M(x) = M(\text{先頭の加数})`$。
  - $`M(\Omega_a) = \Omega_{M(a)}`$。Pohlers の (172) を使う: $`\mathrm{Cl}(\alpha, \beta)`$ が $`[\Omega_\sigma, \Omega_{\sigma +1})`$ と
    交われば $`\Omega_\sigma \in \mathrm{Cl}(\alpha, \beta)`$。
  - $`M(\psi_{I_n}(y))`$ は $`\psi_{I_n}(y)`$、$`I_n`$、$`\psi_{I_n}(M(y))`$ のどれかである。
  - $`M(\psi_{\Omega_{s+1}}(y))`$ は $`\psi_{\Omega_{s+1}}(y)`$、$`\Omega_{s+1}`$、$`\Omega_{M(s)}`$、
    $`\psi_{\Omega_{s+1}}(M(y))`$ のどれかである。
  - $`a \in R`$ なら $`M(\varphi (a, b)) = \varphi (a, M(b))`$。そうでないなら $`M(\varphi (a, b)) = \varphi (M(a), M(q))`$。
    ここで $`q`$ は $`b \lt \varphi (M(a), q)`$ となる最小の順序数である。

  よって $`M(\xi)`$ は値である。使う崩壊は、引数が $`\xi`$ より小さいものだけである。
- **$`K`$ の健全性の逆**（Pohlers の (178) のもう半分）: $`t \in \mathrm{NF}`$ で
  $`\lvert t\rvert \in \mathrm{Cl}(\lvert \alpha \rvert, \lvert \mu \rvert)`$ なら $`K_\mu (t) \lt \alpha`$（`Term.KLt_complete`）。崩壊の場合は
  `arg_mem_of_psi_mem` である: $`\psi_\kappa (d) \in \mathrm{Cl}(\alpha, \beta)`$、$`\beta \le \psi_\kappa (d)`$、$`d \in \mathrm{Cl}(d, \psi_\kappa (d))`$ なら、
  $`d \in \mathrm{Cl}(\alpha, \beta)`$ かつ $`d \lt \alpha`$。閉包は $`\psi_\kappa (d)`$ を、$`e \in \mathrm{Cl}(\alpha, \beta)`$、$`e \lt \alpha`$ による
  $`\psi_\kappa (e)`$ として作った。このとき $`d = M(e)`$ であり、$`M`$ は $`\mathrm{Cl}(\alpha, \beta)`$ から出ない
  （`MQ_of_mem_CSet`）。$`\mu = \psi_\kappa (M(\xi))`$、$`\alpha = M(\xi)`$ とすると、
  $`M(\xi) \in \mathrm{Cl}(M(\xi), \psi_\kappa (M(\xi)))`$ が $`\psi_\kappa (M(\xi))`$ の $`\mathrm{NF}`$ の条件になる。

## 5. ここでしていないこと

- **完全性**は証明した: `Term.vals_eq`（§4）。主張は $`\bigcup_a \mathrm{Cl}(a, 0)`$ についてである。
  この集合が $`\mathrm{Cl}(\varepsilon_{I_\omega +1}, 0)`$（または別の上限つきの閉包）と等しいことは証明していない。
- **再帰的正則順序数。** Buchholz や Pohlers と同じく、基数は本当の
  基数である。それを再帰的正則順序数に置き換えることは試みていない。
- **Wilken の主張。** この体系の可算な部分が $`\mathrm{Core}(R_2^+)`$ を覆うかどうかは
  未解決である。これは、知られている数学を形式化しても決まらない。Wilken はこれを証明なしの
  主張として書いている（*A glimpse of Σ₃-elementarity*, 2020, 421 ページ。*Pure
  Σ₂-elementarity beyond the core*, 2021, §1 でもくり返している）。そして $`R_2^+`$ の解析は
  これからの課題で、順序数算術を一般化する方法が要り、その始まりが Weiermann–Wilken 2011
  だと書いている。決めるには、その解析が要る。つまり、$`R_2^+ = (\mathrm{Ord}; 0, +; \le, \le_1, \le_2)`$ の
  有限パターンの isominimal な実現を、この体系のような表記系の項に割り当てることである。
  それをした論文は無い。

## 6. ファイル

| ファイル | 中身 |
|---|---|
| `Hyp.lean` | $`\Omega`$、仮定の構造体 `InaccSeq`、$`R`$、基数と $`\mathrm{SC}`$ についての基本的な事実 |
| `Ord.lean` | $`\mathrm{Cl}`$、$`\psi`$、F1–F4 |
| `Facts.lean` | F5–F12 |
| `Term.lean` | 項、値、項の種類、$`\mathrm{card}`$、$`K`$、比較、$`\mathrm{NF}`$ |
| `Correct.lean` | $`K`$ の健全性、主定理 |
| `CNF.lean` | 先頭の加数、主加数 `Comp`、$`v \lt \varphi (c, q)`$ となる最小の $`q`$ である `q0(c, v)` |
| `Struct.lean` | 上界 $`\Lambda`$、(172)、$`\mathrm{Cl}(\alpha, \beta)`$ の元の形 |
| `NFM.lean` | $`M`$、その計算、$`M`$ が $`\mathrm{Cl}(\alpha, \beta)`$ から出ないこと、`arg_mem_of_psi_mem` |
| `Onto.lean` | $`K`$ の健全性の逆、`addNF`、完全性: `Term.vals_eq`、`Term.existsUnique_NF` |
