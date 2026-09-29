[← 戻る](../POR-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# トリオ数列をパターンに変換する

トリオ数列（3 行のバシク行列）を、Carlson の階数 2 のパターン（"Patterns of resemblance of order 2", APAL 158, 2009）に変換するプログラムである。背景は [../POR-ja.md](../POR-ja.md) にある。

## 使い方

### トリオ数列 → パターン

```
python3 phi3def2.py "(0,0,0)(1,1,1)(1,1,0)(2,2,1)"
```

出力：

```
0 a (n0 (*n1 ([n2 n3])))
```

- パターンの元を、小さい順に左から並べる：`0`、`a`（= 1）、`n0`、`n1`、…。和は `n1+n0` のように書く。
- `*` の付いた元が、入力を表す元である。
- `(x … z)` は $`x \le_1 z`$、`[x … z]` は $`x \le_2 z`$ を表す。

### パターン → トリオ数列

この向きのプログラムは、まだ無い。

## アルゴリズム

GitHub は 1 ページに限られた量の数式しか表示しないので、アルゴリズムを 2 つに分ける。A.1–A.8 は下にあり、
A.9–A.21 は [ALGORITHM-2-ja.md](ALGORITHM-2-ja.md) にある。ここからは A.9–A.21 のラベルを節の番号で指す。

アルゴリズムは、分岐の入れ子の箇条書きで書く。各関数は、まず入力と出力を 1 文で述べる。次に、その分岐を
コードと同じ順に並べ、(C2-5-1) のようなラベルを付ける。ラベルは関数の名前で始まるので、1 つの関数の
ラベルは 1 つの並びになる。「そうでなければ」は、いつも「同じ深さの前の分岐のどれにも当てはまらない
ならば」の意味である。

### A.1 約束

- **項**は $`s = (y, z, B)`$ である。$`y = y(s)`$ は列の行 1 の成分（**段**）、$`z = z(s)`$ は行 2 の成分、
  $`B = \mathrm{ch}(s) = (B_1, \ldots, B_k)`$ は順に並んだ子である。行 0 の成分は木の深さであり、
  持たない。
- $`1 = (0, 0, ())`$ は行列 $`(0,0,0)`$ である。$`1`$ に等しい子を**単位**と呼ぶ。
- **和**は項の有限列 $`(t_1, \ldots, t_n)`$ である。$`()`$ は $`0`$ である。列 $`B`$ に対して
  $`\mathrm{root}(B) = (0, 0, B)`$ とする。
- $`(A, B)`$ は列 $`A`$ と $`B`$ をつないだもの、$`U^m`$ は $`U`$ を $`m`$ 個並べた列である。よって
  $`\mathrm{root}(A, U^m)`$ は、子が $`A`$ と $`m`$ 個の $`U`$ である根の項である。$`A + B`$ はいつも A.2 の和で
  あり、つなぐことではない。
- 列は木の中の場所である。「最初の 1 段上の子」「最後の子」「並びの成分である」などの言葉は場所を指す。
  $`=`$ は項として比べる。別の場所にある等しい 2 つの列は、別の列である。
- 並びの番号は 1 から数える。$`\bot`$ は「列が無い」を表す並びの成分、$`\mathrm{none}`$ は値が無いことを表す。
- 列 $`K`$ に対して：
  - $`K`$ の **1 段上の子**とは、$`z(c) = 1`$ かつ $`y(c) = y(K) + 1`$ の子 $`c`$ である。$`\mathrm{up}(K)`$ は
    それらを順に並べたものである。
  - $`\mathrm{Rest}(K)`$ は、$`K`$ の他の子を順に並べたものである。
  - $`K`$ の**同じ段の子**とは、$`z(c) = 1`$ かつ $`y(c) = y(K)`$ の子 $`c`$ である。

### A.2 木、順序、和（`tss.py`）

**読み込み。** $`\mathrm{parse}`$ は文字列を読み、列の並びを返す。内側に括弧を含まない "(" … ")" の部分が
それぞれ 1 つの列である。他の文字は無視する。
- (parse-1) もし括弧の中が空白だけならば、列は $`(0)`$ である。
- (parse-2) そうでなければ、列は、中のコンマで区切った整数の並びである。

次に、各列の後ろに 0 を足して長さ 3 にする。4 つ目より後の成分は $`\mathrm{parse}`$ が残すが、後で使わない。

**木。** $`\mathrm{tree}(M)`$ は列の並び $`M_1, \ldots, M_n`$（$`M_i = (x_i, y_i, z_i)`$）を取り、和を返す。
- $`M_i`$ の**親**は、$`j \lt i`$ かつ $`x_j \lt x_i`$ となる一番大きい $`j`$ の $`M_j`$ である。
  - (tree-1) もしそのような $`j`$ があるならば、$`M_i`$ は $`M_j`$ の子である（子は $`i`$ の小さい順）。
  - (tree-2) そうでなければ、$`M_i`$ は**根**である。
- $`M_i`$ の項は $`T(i) = (y_i, z_i, (T(c_1), \ldots, T(c_k)))`$ である。ここで $`c_1 \lt \cdots \lt c_k`$ は
  その子である。
- 根 $`r_1 \lt \cdots \lt r_m`$ に対して $`\mathrm{tree}(M) = (T(r_1), \ldots, T(r_m))`$ とする。これが行列の
  和 $`\hat{M}`$ である。

**順序。** $`\mathrm{cols}(s, e)`$ は、項 $`s`$ を深さ $`e`$ に置いたときの列の並びである。

```math
\mathrm{cols}(s, e) = \bigl((e, y(s), z(s)),\ \mathrm{cols}(B_1, e+1),\ \ldots,\ \mathrm{cols}(B_k, e+1)\bigr)
```

和に対して、$`\mathrm{mat}(t_1, \ldots, t_n)`$ は $`\mathrm{cols}(t_1, 0), \ldots, \mathrm{cols}(t_n, 0)`$ を
つないだものである。これが和の行列である。
- 3 つ組の並びは辞書式に比べる。最初に違う位置で決まり、そこの 3 つ組を辞書式に比べる。一方が他方の
  真の頭の部分なら、それが小さい。
- 項：$`s \lt t`$ とは $`\mathrm{cols}(s, 0) \lt \mathrm{cols}(t, 0)`$ のことである。和：$`\mathrm{mat}`$ で比べる。

**和。** 項の列 $`A`$、$`B`$ に対する $`A + B`$：
- (add-1) もし $`B = ()`$ ならば、$`A + B = A`$ である。
- (add-2) そうでなければ、$`A \ne ()`$ で $`A`$ の最後の項が $`B_1`$ より小さい間、$`A`$ の最後の項を除く。
  そして $`A + B`$ は $`(A, B)`$ である。

$`\Sigma(t_1, \ldots, t_n) = (\cdots((() + (t_1)) + (t_2)) \cdots) + (t_n)`$ は並びの和で、左から足す。
$`\Sigma() = ()`$ とする。

**出力。** $`\mathrm{show}`$ は和をその行列 $`\mathrm{mat}`$ として、列ごとに "(x,y,z)" と書く。

### A.3 基本の関数（D1）

**epsilon の項。** $`\mathrm{eps}(t)`$ は、$`y(t) = 0`$、$`\mathrm{ch}(t) \ne ()`$、かつ $`t`$ の最後の子の
$`y \ge 1`$ のときに真である。

**2 行版の log。** 根の項 $`t`$ に対して、$`H`$ を $`y \ge 1`$ の子、$`O_1, \ldots, O_r`$ を $`y = 0`$ の子とする
（どちらも順のまま）。
- (log-1) もし $`H \ne ()`$ ならば、$`\log(t) = \Sigma(\mathrm{root}(H), O_1, \ldots, O_r)`$ である。
- (log-2) そうでなければ、$`\log(t) = \Sigma(O_1, \ldots, O_r)`$ である。

**2 行版の届く先の増分。** 最後の子が $`B_k`$ の根の項 $`t`$ に対して、$`u = \mathrm{root}(\mathrm{ch}(B_k))`$ とする。
- (lam-1) もし $`\mathrm{eps}(u)`$ ならば、$`\lambda(t) = (u)`$ である。
- (lam-2) そうでなければ、$`\lambda(t) = \log(u)`$ である。

**持ち主を探す。** $`\mathrm{own}(\sigma, y)`$ は、成分の積み重ね $`\sigma`$ と段 $`y`$ を取る。成分は
$`(y_e, h_e)`$ か $`(y_e, h_e, \mathrm{ok}_e)`$ である。$`\omega`$ の列の段、その像のずれ、（C1 では）旗を表す。
$`y_a \le y`$ となる一番上の成分を $`a`$ とする。
- (own-1) もし $`a`$ があり、3 つ目の成分を持ち、$`\mathrm{ok}_a`$ が偽ならば、結果は $`\mathrm{none}`$ である。
- (own-2) もし $`a`$ があり、それ以外ならば、結果は $`a`$ である。
- (own-3) もし $`y_a \le y`$ の成分が無いならば、結果は $`\mathrm{none}`$ である。

**他の小さな関数。**
- $`\mathrm{split}(W) = (\mathrm{hi}, \mathrm{lo})`$：$`\mathrm{hi}`$ は $`W`$ の子のうち $`y \ge 2`$ か $`z = 1`$ のもの、
  $`\mathrm{lo}`$ は残りである（どちらも順のまま）。
- $`\Omega\mathrm{pre}(\mathrm{hi})`$ は、$`\mathrm{hi}`$ の頭の部分で、列がすべて $`z = 1`$ である一番長いものである。
- $`W + k = (y(W), z(W), (\mathrm{ch}(W), 1^k))`$：子の後ろに単位を $`k`$ 個足す。
- $`\mathrm{anchor}(t)`$：
  - (anchor-1) もし $`y(t) = 0`$ で $`t`$ が $`k \ge 2`$ 個の子を持つならば、
    $`\mathrm{anchor}(t) = \mathrm{root}(B_1, \ldots, B_{k-1})`$ である。
  - (anchor-2) そうでなければ、$`\mathrm{anchor}(t) = \mathrm{none}`$ である。

### A.4 潰す操作 C1（D2）

$`\mathrm{C1}_N`$ は Buchholz の潰す操作 $`\Omega_1 \mapsto N`$ を、持ち主の積み重ねとともに読むものである。

$`\mathrm{C1}_N(s;\ \sigma, \mathrm{last}, \mathrm{mn})`$ は、根の項 $`N`$、列 $`s = (y, z, B)`$、成分 $`(y_e, h_e, \mathrm{ok}_e)`$ の積み重ね $`\sigma`$ または印 $`\mathrm{fin}`$、2 つの旗を取る。結果は項か、**包んだ**列 $`[\![c]\!]`$（段 1 の列の中に入れる列）である。
- (C1-1) もし $`y = 0`$ ならば、結果は $`s`$ である。
- (C1-2) そうでなければ、$`\sigma = \mathrm{fin}`$ のとき真となる旗を $`\varphi`$ とする。$`\varphi`$ が真なら $`\sigma`$ を空の積み重ねに置き換える。そして：
  - (C1-2-1) もし $`z = 1`$ かつ $`\sigma \ne ()`$ ならば：ここで $`h`$ を $`\sigma`$ の一番上の成分のずれ、$`\mathrm{ok}`$ をその旗とする（旗が無ければ $`\mathrm{ok} = \mathrm{true}`$）。結果は $`(y - h,\ 1,\ \mathrm{C1s}_N(B;\ (\sigma, (y, h, \mathrm{ok})), \mathrm{last}))`$ である。
  - (C1-2-2) もし $`z = 1`$ かつ $`\sigma = ()`$ ならば：ここで $`\mathrm{ok} = \lnot\varphi \lor \mathrm{mn}`$ とする。
    - (C1-2-2-1) もし $`y = 2`$ ならば、結果は包んだ列 $`[\![(2,\ 1,\ \mathrm{C1s}_N(B;\ ((2, 0, \mathrm{ok})), \mathrm{last}))]\!]`$ である。
    - (C1-2-2-2) そうでなければ、結果は $`(y - 1,\ 1,\ \mathrm{C1s}_N(B;\ ((y, 1, \mathrm{ok})), \mathrm{last}))`$ である。
  - (C1-2-3) もし $`z \ne 1`$ ならば：ここで $`a = \mathrm{own}(\sigma, y)`$ とする。
    - (C1-2-3-1) もし $`a \ne \mathrm{none}`$ で、かつ「$`\mathrm{last}`$、$`B = ()`$、$`y = y_a`$、$`a`$ が $`\sigma`$ の一番下の成分そのもの（等しい別の成分ではない）」がそろわないならば、結果は $`(y - h_a,\ 0,\ \mathrm{C1s}_N(B;\ \sigma, \mathrm{last}))`$ である。除いた場合は $`\Omega_1`$ 倍である。一番外の $`\omega`$ の列と同じ段にある、最後の子の無い印である。
    - (C1-2-3-2) そうでなければ、ここで $`K = \mathrm{C1s}_N(B;\ \mathrm{fin}, \mathrm{last})`$ とする。もし $`y = 1`$ ならば、結果は $`\mathrm{root}(\mathrm{ch}(N) + K)`$ である。
    - (C1-2-3-3) そうでなければ、結果は $`(y - 1,\ 0,\ K)`$ である。

$`\mathrm{C1s}_N(B;\ \sigma, \mathrm{last}, l)`$ は並び $`B = (B_1, \ldots, B_k)`$ の上の C1 である。$`l`$ は旗 $`\mathrm{last}`$ を受け取る位置である（与えられなければ $`l = k`$）。$`i = 1, \ldots, k`$ に対して、$`z(B_i) = 1`$、$`i \lt k`$、$`z(B_{i+1}) = 1`$、$`\mathrm{ch}(B_{i+1}) = ()`$ のとき真となる旗を $`\mathrm{mn}_i`$ とし、$`r_i = \mathrm{C1}_N(B_i;\ \sigma, \mathrm{last} \land i = l, \mathrm{mn}_i)`$ とする。$`i = 1, \ldots, k`$ の順に並び $`O`$ を作る。
- (C1s-1) もし $`r_i`$ が包んだ列ならば：
  - (C1s-1-1) もし $`O`$ の最後の成分が包んだ列の群ならば、$`r_i`$ の列をその群の最後に足す。
  - (C1s-1-2) そうでなければ、$`r_i`$ の列を持つ新しい群を足す。
- (C1s-2) そうでなければ、$`r_i`$ を $`O`$ に足す。

結果は $`O`$ の $`\Sigma`$ である。ここで群 $`(c_1, \ldots, c_p)`$ は項 $`(1, 0, (c_1, \ldots, c_p))`$ として数える。（積み重ね $`\sigma`$ はどの $`B_i`$ にも同じである。$`\sigma = \mathrm{fin}`$ なら、どの $`B_i`$ も $`\mathrm{fin}`$ を受け取る。）

$`\mathrm{c1fixed}(G;\ N, \mathrm{last})`$ は、$`G \ne ()`$ かつ $`\mathrm{C1s}_N(G;\ (), \mathrm{last}) = ((1, 0, G))`$ のときに真である。

### A.5 読みの文脈

潰す操作 C2 と、同じ段の $`\omega`$ の列の読み（A.6、A.7）は、**読みの文脈** $`\rho = (\rho_C, \rho_D, \rho_1)`$ を取る。どの部分も $`\mathrm{none}`$ か、次のものである。
- $`\rho_C = (c, \ell_C, \Delta_C)`$：読んでいる $`\omega`$ の列は節点 $`c`$ に属し、段は $`\ell_C`$、段の並びは $`\Delta_C`$ である（A.7）。
- $`\rho_D = (x', \ell')`$：$`\le_2`$ になりうる節点 $`x'`$ の段の列を読んでいる。$`\ell'`$ はその列 $`D`$ の段である（A.13）。
- $`\rho_1 = (d, \kappa)`$：読みは後者 $`d`$ に属し、$`\kappa`$ は次の段の列（または $`\mathrm{none}`$）である。

分岐が特に言わない限り、文脈はそのまま下へ渡す。**$`\mathrm{lh}`$（A.17）の計算は、どれも空の文脈 $`\rho_\varnothing = (\mathrm{none}, \mathrm{none}, \mathrm{none})`$ から始める。** 別の計算の中から呼ばれたときも同じである。

### A.6 潰す操作 C2（D3）

$`\mathrm{C2}_x`$ は $`\Omega_\omega \mapsto x`$、$`\Omega_{\omega+j} \mapsto \Omega_j`$ である。どの印も、それを持つ $`\omega`$ の列の行き先へ潰れる。

$`\mathrm{C2}_x(s;\ \ell, \sigma, \mathrm{last};\ \rho)`$ は、根の項 $`x`$（行き先）、列 $`s = (y, z, B)`$、潰している $`\omega`$ の列 $`D`$ の段 $`\ell`$、成分 $`(y_e, h_e)`$ の積み重ね $`\sigma`$、旗、文脈を取る。結果は項である。
- (C2-1) もし $`y = 0`$ ならば、結果は $`s`$ である。
- (C2-2) もし $`z = 1`$、$`\rho_D = (x', \ell')`$、$`y = \ell'`$、$`y \lt \ell`$ ならば（段の列の奥にある $`D`$ の段の $`\omega`$ の列）：ここで $`\rho'`$ を、$`\rho`$ の $`\rho_D`$ を $`\mathrm{none}`$ に置き換えたものとする。
  - (C2-2-1) もし $`x'`$ が $`\le_2`$ になりうり（A.13、その $`U'`$、$`q'`$、最後の $`\omega`$ の列 $`D'`$）、かつ $`\mathrm{kdl}(D', L(D')) = s`$（A.11）ならば、結果は $`\mathrm{Kimg}(s;\ x', \ell', (\delta'_1, \ldots, \delta'_{q'}), \mathrm{none}, \mathrm{last}, \mathrm{none}, \mathrm{true};\ \rho')`$ である。ここで $`\delta'_i = (\mathrm{ch}(x'), U'^i)`$ とする。
  - (C2-2-2) そうでなければ、結果は $`\mathrm{Kimg}(s;\ x', \ell', \mathrm{ch}(x'), \mathrm{none}, \mathrm{last};\ \rho')`$ である。土台は 1 つの $`\mathrm{ch}(x')`$ である。
- (C2-3) もし $`z = 1`$、$`\rho_C = (c, \ell_C, \Delta_C)`$、$`y = \ell_C`$、$`y = \ell`$ ならば、結果は $`\mathrm{Kimg}(s;\ c, \ell_C, \Delta_C, \mathrm{none}, \mathrm{last};\ \rho)`$ である。
- (C2-4) もし $`z = 1`$ で、上のどれでもないならば：
  - (C2-4-1) もし $`\sigma \ne ()`$ ならば、ここで $`h`$ をその一番上の成分のずれとする。結果は $`(y - h,\ 1,\ \mathrm{C2s}_x(B;\ \ell, (\sigma, (y, h)), \mathrm{last};\ \rho))`$ である。
  - (C2-4-2) もし $`\sigma = ()`$ かつ $`y - \ell \le 1`$ ならば、結果は $`(1,\ 0,\ ((2,\ 1,\ \mathrm{C2s}_x(B;\ \ell, ((y, y - 2)), \mathrm{last};\ \rho))))`$ である。
  - (C2-4-3) そうでなければ、結果は $`(y - \ell,\ 1,\ \mathrm{C2s}_x(B;\ \ell, ((y, \ell)), \mathrm{last};\ \rho))`$ である。
- (C2-5) もし $`z \ne 1`$ ならば：ここで $`a = \mathrm{own}(\sigma, y)`$ とする。
  - (C2-5-1) もし $`a \ne \mathrm{none}`$ で、かつ「$`\mathrm{last}`$、$`B = ()`$、$`y = y_a`$、$`y_a - h_a = 2`$」がそろわないならば、結果は $`(y - h_a,\ 0,\ \mathrm{C2s}_x(B;\ \ell, \sigma, \mathrm{last};\ \rho))`$ である。
  - (C2-5-2) もし $`a \ne \mathrm{none}`$ ならば（除いた場合がそろう。持ち主が 2 段上にある最後の子の無い印は、$`D`$ に対して読む）：ここで $`j = y - \ell`$、$`K = \mathrm{C2s}_x(B;\ \ell, \sigma, \mathrm{last};\ \rho)`$ とする。
    - (C2-5-2-1) もし $`j \le 0`$ ならば、結果は $`\mathrm{root}(\mathrm{ch}(x) + K)`$ である。
    - (C2-5-2-2) そうでなければ、結果は $`(j,\ 0,\ K)`$ である。
  - (C2-5-3) もし $`a = \mathrm{none}`$ かつ $`y \lt \ell`$ ならば、結果は $`\mathrm{root}(\mathrm{ch}(x) + \mathrm{C1s}_x(B;\ (), \mathrm{false}))`$ である。
  - (C2-5-4) そうでなければ、ここで $`K = \mathrm{C2s}_x(B;\ \ell, (), \mathrm{last};\ \rho)`$ とする。
    - (C2-5-4-1) もし $`y = \ell`$ ならば、結果は $`\mathrm{root}(\mathrm{ch}(x) + K)`$ である。
    - (C2-5-4-2) そうでなければ、結果は $`(y - \ell,\ 0,\ K)`$ である。

$`\mathrm{C2s}_x(B;\ \ell, \sigma, \mathrm{last};\ \rho)`$ は並び $`B = (B_1, \ldots, B_k)`$ の上の C2 である。$`r_i = \mathrm{C2}_x(B_i;\ \ell, \sigma, \mathrm{last} \land i = k;\ \rho)`$ とする。$`i = 1, \ldots, k`$ の順に並び $`O`$ を作る。
- (C2s-1) もし $`z(B_i) = 1`$、$`\sigma = ()`$、$`r_i = (1, 0, R)`$、$`O \ne ()`$ で、$`O`$ の最後の成分 $`o`$ が $`y(o) = 1`$、$`z(o) = 0`$、$`\mathrm{ch}(o) \ne ()`$ を満たし最後の子の $`z = 1`$ であり、かつ $`n = |O|`$ に対して $`z(B_n) = 1`$（位置が今の $`O`$ の長さである入力の列）ならば、$`o`$ を $`(1, 0, (\mathrm{ch}(o), R))`$ に置き換える。（続いた包んだ $`\omega`$ の列は、1 つの $`U`$ の形にまとめる。）
- (C2s-2) そうでなければ、$`r_i`$ を $`O`$ に足す。

結果は $`\Sigma(O)`$ である。

### A.7 同じ段の $`\omega`$ の列の読み（D3）

**段の並び** $`\Delta`$ は、子の並びの並び $`(\Delta_1, \ldots, \Delta_n)`$（A.13 の段 $`\delta_m = \mathrm{ch}(d_m)`$）か、**1 つの土台** $`b`$（子の並び 1 つ）である。

$`\mathrm{KI}(B;\ x, \ell, \Delta, t_0, \mathrm{last};\ \rho)`$ は、同じ段の $`\omega`$ の列の子 $`B = (B_1, \ldots, B_k)`$ を読む。$`x`$ は根の項、$`\ell`$ は段、$`t_0`$ は項か $`\mathrm{none}`$ である。結果は和である。並び $`O`$ と、保留の並び $`R`$ を持つ。どちらも初めは空である。旗 $`f`$ で**流す**とは、$`R \ne ()`$ なら $`\mathrm{C2s}_x(R;\ \ell, (), f;\ \rho)`$ の項を $`O`$ に足し、$`R`$ を空にすることである。$`i = 1, \ldots, k`$ について、$`g = B_i`$、$`\mathrm{lg} = \mathrm{last} \land i = k`$ とする。
- (KI-1) もし $`y(g) \ne 0`$ で、「$`z(g) = 1`$ かつ $`y(g) = \ell`$」でなく、「$`z(g) = 0`$ かつ $`y(g) \ge \ell`$」でもないならば、$`g`$ を $`R`$ に足す。
  - (KI-1-1) もし $`i = k`$ ならば、$`\mathrm{lg}`$ で流す。
- そうでなければ、$`\mathrm{false}`$ で流し、次に：
  - (KI-2) もし $`y(g) = 0`$ ならば、$`g`$ を $`O`$ に足す。
  - (KI-3) もし $`z(g) = 1`$ かつ $`y(g) = \ell`$ ならば、$`\mathrm{Kimg}(g;\ x, \ell, \Delta, t_0, \mathrm{lg};\ \rho)`$ を足す。
  - (KI-4) もし $`z(g) = 0`$、$`y(g) = \ell`$、$`\mathrm{ch}(g) = ()`$、$`\mathrm{lg}`$、$`t_0 \ne \mathrm{none}`$ ならば、$`t_0`$ を足す（最後の子の無い印は、1 段上の $`\Omega_1`$ 倍である）。
  - (KI-5) もし $`z(g) = 0`$ かつ $`y(g) = \ell`$ ならば、$`\mathrm{root}(\mathrm{ch}(x) + \mathrm{KI}(\mathrm{ch}(g);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lg};\ \rho))`$ を足す。
  - (KI-6) もし $`z(g) = 0`$ かつ $`y(g) \gt \ell`$ ならば、$`(y(g) - \ell,\ 0,\ \mathrm{KI}(\mathrm{ch}(g);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lg};\ \rho))`$ を足す。
  - (KI-7) そうでなければ、$`\mathrm{C2}_x(g;\ \ell, (), \mathrm{lg};\ \rho)`$ を足す。この場合は起きない。(KI-1) から (KI-6) がすべての列を覆う。

結果は $`\Sigma(O)`$ である。

$`\mathrm{Kimg}(K;\ x, \ell, \Delta, t_0, \mathrm{last}, c, j_0;\ \rho)`$ は、$`y(K) = \ell`$ の同じ段の $`\omega`$ の列 $`K`$ の加数である。$`c`$ は上限（$`\mathrm{none}`$ か整数。与えられなければ $`\mathrm{none}`$）、$`j_0`$ は旗（与えられなければ $`\mathrm{false}`$）である。結果は根の項である。
- (Kimg-1) もし $`\Delta = (\Delta_1, \ldots, \Delta_n)`$ が並びならば：ここで $`B = \mathrm{ch}(K)`$、$`j = \min(\mathrm{lev}(K) - 1,\ n - 1)`$（A.11）、$`V = \mathrm{up}(K)`$ とする。$`\kappa`$（$`K`$ が共有しうる段の列）を次のように定める。
  - (Kimg-1-1) もし $`\rho_1 = (d, \kappa')`$ かつ $`d = x`$ ならば、$`\kappa = \kappa'`$ である。
  - (Kimg-1-2) そうでなく、もし $`x \ne \mathrm{none}`$ で $`x`$ が $`\le_2`$ になりうるならば、$`\kappa = K_1(x)`$（下）である。
  - (Kimg-1-3) そうでなければ、$`\kappa = \mathrm{none}`$ である。

  次に：
  - (Kimg-1-4) もし $`V \ne ()`$、$`\kappa \ne \mathrm{none}`$、$`V_1 = \kappa`$、$`\mathrm{Rest}(V_1) \ne ()`$ ならば（`kbcut`：$`K`$ は $`K_1`$ の段を共有する）、子 $`V_1`$ を $`B`$ から除き、$`j = \min(|V| - 1,\ n - 1)`$ とする。
    - (Kimg-1-4-1) もし $`c \ne \mathrm{none}`$ ならば、$`j = \max(0, \min(j, c))`$ とする（`kb2`）。

    そして子 $`V_2, \ldots, V_{1+j}`$ を $`B`$ から除く。
  - (Kimg-1-5) そうでなく、もし $`j \ne 0`$ か $`V \ne ()`$ ならば、$`K`$ の 1 段上の子をすべて $`B`$ から除く。
  - (Kimg-1-6) もし $`j_0`$ ならば（**規則 `kdl0`**）：ここで $`\Lambda = L(K)`$（A.11）とし、$`j`$ を $`\Lambda_i \ne \bot`$ かつ項として $`\Lambda_i = \Lambda_1`$ となる一番大きい $`i - 1`$（無ければ $`0`$）とし、$`j = \min(j, n - 1)`$ とし、$`B`$ を $`\mathrm{ch}(K)`$ から 1 段上の子を除いたものとする。理由：年上の兄弟の後に読む（または同じ段の子の中に入れ子になった）$`D`$ の段の $`\omega`$ の列は、その最後の鎖の一番下の段で読み、その一番上より上では読まない。

  結果は $`\mathrm{root}(\Delta_{1+j} + \mathrm{KI}(B;\ x, \ell, \Delta, t_0', \mathrm{last};\ \rho))`$ である。ここで $`\mathrm{last}`$ なら $`t_0' = t_0`$、そうでなければ $`t_0' = \mathrm{none}`$ とする。
- (Kimg-2) そうでなければ（$`\Delta = b`$ は 1 つの土台）、結果は $`\mathrm{root}(b + \mathrm{KI}(\mathrm{ch}(K);\ x, \ell, b, t_0', \mathrm{last};\ \rho))`$ である。$`t_0'`$ は上と同じである。

$`\le_2`$ になりうる $`x`$ に対して、$`K_1(x)`$ はその列 $`D`$（A.13）の最初の 1 段上の子である。$`D`$ が 1 段上の子を持たなければ $`\mathrm{none}`$ である。

$`\mathrm{shares}(g, K_1)`$ は、$`\mathrm{up}(g) \ne ()`$ かつ $`g`$ の最初の 1 段上の子が $`K_1`$ に等しいときに真である。

### A.8 根の $`\omega`$ の並びのコピー（D4）

$`\mathrm{Up}(a;\ N, \mathrm{last})`$ は、根の $`\omega`$ の列 $`a`$ を 1 段上げる。$`N`$ は根の項である。$`r(s, Y, \mathrm{lst})`$ を使う。ここで $`s = (y, z, B)`$ は列、$`Y`$ は段の並び（$`s`$ より上の $`\omega`$ の列の段）、$`\mathrm{lst}`$ は旗である。
- (Up-1) もし $`y = 0`$ ならば、$`r = s`$ である。
- (Up-2) もし $`\mathrm{lst}`$、$`B = ()`$、$`z = 0`$、$`N \ne \mathrm{none}`$ ならば：ここで $`Y'`$ を、$`Y`$ の成分 $`o`$ のうち $`o \le y`$ のものを順に並べたものとする。もし $`Y' \ne ()`$ で、（$`|Y'| = 1`$、または $`Y'`$ の成分がすべて $`y`$ で $`\max Y \gt y`$）であり、$`Y'`$ の最後の成分が $`y`$ で、$`Y_1 = y`$ ならば、$`r = N`$ である（最後の印は $`\Omega_1`$ 倍の $`N`$ である）。この条件が成り立たなければ、(Up-3) へ進む。
- (Up-3) そうでなければ、$`z = 1`$ なら $`Y'' = (Y, y)`$、そうでなければ $`Y'' = Y`$ とする。$`r = (y + 1,\ z,\ (r(B_1, Y'', \mathrm{lst} \land 1 = k), \ldots, r(B_k, Y'', \mathrm{lst} \land k = k)))`$ である。旗は最後の子だけに渡る。

$`\mathrm{ch}(a) = (B_1, \ldots, B_k)`$ に対して、$`\mathrm{Up}(a;\ N, \mathrm{last}) = (2,\ 1,\ (r(B_i, (y(a)), \mathrm{last} \land i = k))_{i = 1, \ldots, k})`$ とする。

アルゴリズムは [ALGORITHM-2-ja.md](ALGORITHM-2-ja.md)（A.9–A.21）に続く。
