[← 戻る](README-ja.md) | [English](ALGORITHM-2.md) | [Japanese](ALGORITHM-2-ja.md)

# トリオ数列をパターンに変換する：アルゴリズムの後半

これは `phi3def2.py` のアルゴリズムの 2 つ目の部分である。主な手続き（手順 1–6）と操作 A.1–A.8 は [README-ja.md](README-ja.md#step-1) にある。

<a id="a9"></a>
### A.9 $`\le_2`$ になりうる節点の届く先（D9）

$`\mathrm{lh}_1(x)`$ は、$`\le_2`$ になりうる根の項 $`x`$（A.3 の $`A`$、$`P`$、$`W`$、$`U`$、$`q`$、$`G`$、$`D`$、$`\Lambda`$、$`d_m`$、$`\delta_m`$）を取ってその $`\le_1`$ の届く先（和）を返し、(lh-6) から呼ばれる。(LG-3) で記録する $`\mathrm{pre}(x)`$ は (lh-3-2) が使う。ここで $`r = \mathrm{lev}(D)`$、$`S = (d_q)`$ とする。
- (lh1-1) もし $`q \lt r`$ ならば（入れ子）、$`\mathrm{lh}_1(x) = \mathrm{lh}(\mathrm{root}(P, W + 1))`$ である。
- ここで $`(a, b)`$ を $`G`$ の最後の組とし、枠の土台を $`b_0 = \delta_q`$ とする。
- (lh1-2) もし $`q \ge 2`$、$`n = 1`$、$`|\Lambda| \ge q`$、$`\Lambda_q = \bot`$、$`\Lambda_{q-1} \ne \bot`$ で、$`\Lambda_{q-1}`$ が同じ段の子を持ち、$`D`$ のどの 1 段上の子も（場所として）$`\Lambda`$ の成分であるならば、$`b_0 = \delta_{q-1}`$ とする（段 $`q`$ は自分の一番上の段である）。
- (lh1-3) もし $`\mathrm{d1}(d_q) \ne \mathrm{none}`$ ならば、$`S = \mathrm{lh}(d_q)`$ とする。
- $`m = 1, \ldots, q - 1`$ について（自分の読みを持つ $`d_m`$ の一番大きい届く先）：
  - (lh1-4) もし $`\mathrm{d1}(d_m) = (x, K, m, q)`$、$`m \lt q`$、$`\mathrm{chtop}(K)`$ ならば、この $`m`$ を飛ばす。
  - (lh1-5) そうでなく、もし $`\mathrm{d1}(d_m) \ne \mathrm{none}`$ ならば、ここで $`L = \mathrm{lh}(d_m)`$ とする。
    - (lh1-5-1) もし $`L \succ S`$ ならば、$`S = L`$ とする。
- ここで $`\Delta = (\delta_1, \ldots, \delta_q)`$ とし、$`|A| \ge 2`$ なら $`t_0 = \mathrm{root}(P)`$、そうでなければ $`t_0 = \mathrm{none}`$ とする。そして $`\mathrm{lh}_1(x) = \mathrm{LG}(S)`$ である。

$`\mathrm{LG}(S)`$ は、最後の組の読み、一番上の読み、塊を $`S`$ に畳み込む。
- (LG-1) $`i = a, \ldots, b`$ について、$`\ell = y(G_i)`$ として：
  - (LG-1-1) もし $`i \lt b`$、$`\mathrm{lim}(G_i)`$、（$`\mathrm{lev}(G_i) \gt \mathrm{lev}(G_b)`$ か $`\mathrm{cont}(G_i)`$）で、$`\mathrm{cov}(G_i, G_b)`$ でないならば：ここで $`e = \mathrm{root}(\delta_q + ((1, 0, (\mathrm{limx}(G_i, x)))))`$（$`G_i`$ の塊）とし、$`e`$ を $`x`$ の下に記録し、$`S = S \oplus e`$ とする。
  - (LG-1-2) そうでなければ、$`S = \mathrm{F}(S;\ x, G_i, \ell, b_0, \Delta, t_0, i = n;\ ((x, \ell, \Delta), \mathrm{none}, \mathrm{none}))`$ とする。
- (LG-2) $`m = 1, \ldots, |\Lambda|`$ について（一番上の読み）：
  - (LG-2-1) もし $`\Lambda_m = \bot`$、$`m \ge q`$、$`\mathrm{chtop}(\Lambda_m)`$ が偽、のどれかならば、この $`m`$ を飛ばす。
  - (LG-2-2) そうでなければ、ここで $`K = \Lambda_m`$、$`R = \mathrm{LK}(x, K, m)`$、$`\Delta' = (\delta_{m+1}, \ldots, \delta_q)`$ とし、$`m \lt |\Lambda|`$ かつ $`\Lambda_{m+1} \ne \bot`$ なら $`\kappa = \Lambda_{m+1}`$（そうでなければ $`\kappa = \mathrm{none}`$）とする。$`\rho = ((d_m, y(K), \Delta'),\ (x, y(D)),\ (d_m, \kappa))`$ として、$`S = \mathrm{F}(S;\ d_m, (y(K), z(K), R), y(K), \delta_q, \Delta', \mathrm{none}, \mathrm{true};\ \rho)`$ とする。
- (LG-3) $`\Lambda`$ の $`\bot`$ でない各成分 $`K`$ について、$`V = \mathrm{up}(K)`$ として：
  - (LG-3-1) もし $`|V| \ge 2`$ で $`\mathrm{sub}(V_1)`$ の最後の成分が切れていないならば：ここで $`E`$ を、$`V_2, V_3, \ldots`$ のうち $`c \ne V_1`$ の $`c`$ とする。
    - (LG-3-1-1) もし $`|E| = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$ ならば、$`S = S \oplus d_q`$ とする（倍にする）。

  $`\mathrm{pre}(x) = S`$ を記録する（lh-3-2 が使う）。
- (LG-4) **名前の付いた場合 `lnest`。** もし $`a \ge 3`$、$`\mathrm{lim}(G_{a-1})`$、$`\mathrm{cont}(G_{a-1})`$ ならば：ここで $`e = \mathrm{root}(\delta_q + ((1, 0, (G_1, \ldots, G_{a-2}, \mathrm{limx}(G_{a-1}, x)))))`$ とし、$`e`$ を $`x`$ の下に記録し、$`S = S \oplus e`$ とする。理由：前の加数たちは 1 つの $`U`$ の形であり、その段はそれらの最後のものの段である。
- (LG-5) そうでなければ、$`i = 1, \ldots, a - 1`$ について：
  - (LG-5-1) もし $`\mathrm{lim}(G_i)`$ かつ $`\mathrm{cont}(G_i)`$ ならば、ここで $`e = \mathrm{root}(\delta_q + ((1, 0, (\mathrm{limx}(G_i, x)))))`$ とし、$`e`$ を $`x`$ の下に記録し、$`S = S \oplus e`$ とする。

結果は $`S`$ である。

<a id="a10"></a>
### A.10 段の列の子の読み（D8）

$`\mathrm{LK}(x, K, m)`$ は、$`\le_2`$ になりうる $`x`$（その $`U`$、$`q`$、$`D`$、$`\Lambda`$）と、その段の列 $`K = K_m`$ と $`m`$ を取り、$`K`$ の子を読んで列の並びを返し、(lh-3-3) と (LG-2-2) から呼ばれる。LK の中の読みは、どれも空の文脈 $`\rho_\varnothing`$ を使う。

ここで $`R = \mathrm{Rest}(K)`$ とする。**持ち主の表** $`w`$ を次のように作る。$`w(y(D)) = 0`$ とする。次に $`i = 1, \ldots, m - 1`$ について、$`\Lambda_i \ne \bot`$ かつ $`y(\Lambda_i) \lt y(K)`$ なら $`w(y(\Lambda_i)) = i`$ とする（後の $`i`$ が前のものを置き換える）。$`R`$ の各 $`c`$ を $`\mathrm{OL}(c)`$ に、次に $`\mathrm{OD}(c)`$（下）に置き換える。次に $`R`$ の各 $`c`$ について順に：
- (LK-1) もし $`z(c) = 1`$ かつ $`y(c) = y(D)`$ ならば：ここで $`c`$ が $`K`$ の最初の子でない（年上の兄弟を持つ）とき真となる旗を $`j_0`$ とし、$`e = \mathrm{Kimg}(c;\ x, y(D), (\delta_1, \ldots, \delta_q), \mathrm{none}, \mathrm{false}, m - 2, j_0;\ \rho_\varnothing)`$ とする。$`e`$ を $`x`$ の下に記録し、$`c`$ を $`(0, 0, \mathrm{ch}(e))`$ に置き換える。
- (LK-2) そうでなければ、$`c`$ をそのままにする。

次に $`R`$ の各 $`c`$ について順に：
- (LK-3) もし $`z(c) = 1`$、$`m \ge 2`$、$`y(c) \lt y(K)`$ ならば：ここで $`p`$ を、$`\Lambda_i \ne \bot`$ かつ $`y(\Lambda_i) = y(c)`$ となる $`i \le m - 1`$ の一番大きいものとする。
  - (LK-3-1) もし $`p`$ があるならば、ここで $`\Delta' = (\delta_{p+1}, \ldots, \delta_{m-1})`$ とする。
    - (LK-3-1-1) もし $`\Delta' \ne ()`$ ならば、$`e = \mathrm{Kimg}(c;\ x, y(c), \Delta', \mathrm{none}, \mathrm{false};\ \rho_\varnothing)`$ とし、$`e`$ を $`x`$ の下に記録し、$`c`$ を $`(0, 0, \mathrm{ch}(e))`$ に置き換える。

結果は $`R`$ である。

$`\mathrm{OL}(c)`$ は、$`D`$ か前の段の列が持ち主の印を読む。
- (OL-1) もし $`z(c) = 0`$、$`y(c) \ge 1`$ で、$`j = w(y(c))`$ が定まっているならば：
  - (OL-1-1) もし $`\mathrm{ch}(c) = ()`$ ならば、結果は $`(0, 0, \delta_j)`$ である。
  - (OL-1-2) そうでなければ、ここで $`e = \mathrm{root}(\delta_j + \mathrm{C2s}_{d_j}(\mathrm{ch}(c);\ y(c), (), \mathrm{true};\ \rho_\varnothing))`$（$`d_j`$ の上の枠）とし、$`e`$ を $`x`$ の下に記録する。結果は $`(0, 0, \mathrm{ch}(e))`$ である。
- (OL-2) そうでなければ、結果は $`c`$ である。

$`\mathrm{OD}(c)`$ は、$`K`$ の同じ段の子の中に入れ子になった、子の無い印に同じことをする。
- (OD-1) もし「$`z(c) = 1`$ かつ $`y(c) = y(K)`$」でないならば、結果は $`c`$ である。
- (OD-2) そうでなければ、結果は $`\mathrm{rec}(c)`$ である。$`\mathrm{rec}(t)`$ は、$`t`$ の各子 $`g`$ を次のように置き換えたものである。
  - (OD-2-1) もし $`z(g) = 0`$、$`\mathrm{ch}(g) = ()`$、$`w(y(g))`$ が定まり、$`y(g) \lt y(K)`$ ならば、$`(0, 0, \delta_{w(y(g))})`$ に置き換える。
  - (OD-2-2) そうでなく、もし $`z(g) = 1`$ かつ $`y(g) = y(K)`$ ならば、$`\mathrm{rec}(g)`$ に置き換える。
  - (OD-2-3) そうでなければ、$`g`$ をそのままにする。

<a id="a11"></a>
### A.11 列の子の畳み込み（D8）

$`\mathrm{F}(S;\ x, G, \ell, b, \Delta, t_0, \mathrm{lastG};\ \rho)`$ は、和 $`S`$ と列 $`G`$ を取り、$`G`$ の子の読みを $`S`$ に畳み込んで新しい和を返し、(lh-3-3)、(LG-1-2)、(LG-2-2) から呼ばれる。$`x`$ は読みが属する根の項、$`\ell`$ は段、$`b`$ は枠の土台（子の並び）、$`\Delta = (\Delta_1, \ldots, \Delta_n)`$ は段の並び、$`t_0`$ は項か $`\mathrm{none}`$ である。添字の像の並び $`I`$ を持ち、初めは空である。ここで $`V`$ を $`z = 1`$ かつ $`y = \ell + 1`$ の $`G`$ の子とし、$`V \ne ()`$ なら $`H = \mathrm{sub}(V_1)`$（そうでなければ $`H = ()`$）とする。$`H \ne ()`$ で $`H`$ の最後の成分が切れていないなら、$`E`$ を、$`V_2, V_3, \ldots`$ のうち（場所として）$`H`$ の成分でなく $`c \ne V_1`$ である $`c`$ とする。そうでなければ $`E = ()`$ とする。$`|E| = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$ のとき真となる旗を $`\beta`$ とする（**子の無いさらなる 1 段上の子 1 つ**）。$`G`$ の各子 $`c`$ について順に、$`\mathrm{lst}`$ を「$`\mathrm{lastG}`$ かつ $`c`$ が最後の子」として：
- (F-1) もし $`\beta`$、$`c`$ が $`E_1`$、$`n \ge 1`$、$`\mathrm{ch}(x) \ne \Delta_1`$ ならば（倍にする）：$`\mathrm{ch}(c) = ()`$ なら $`S = S \oplus \mathrm{root}(\Delta_n)`$ とする。そうでなければ $`S = S \oplus \mathrm{root}(\Delta_n + \mathrm{KI}(\mathrm{ch}(c);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lst};\ \rho))`$ とする（後の場合は起きない。$`\beta`$ なら $`c`$ は子を持たない）。次の子へ進む。
- (F-2) もし $`c = 1`$ で、$`c`$ が最初の子でなく、その前の子 $`c'`$ が $`z(c') = 1`$、$`y(c') = \ell + 1`$、$`\mathrm{em}(c', \ell)`$ を満たすならば、$`c`$ を飛ばす（極限の段の列の後の単位は吸収される）。
- (F-3) もし $`z(c) = 1`$ ならば：
  - (F-3-1) もし $`y(c) = \ell`$ ならば、$`S = S \oplus \mathrm{Kimg}(c;\ x, \ell, \Delta, t_0, \mathrm{lst};\ \rho)`$ とする。
  - (F-3-2) そうでなければ、何もしない（それは段である）。
- (F-4) もし $`y(c) \gt \ell`$ ならば（添字の列）：$`\mathrm{KI}((c);\ x, \ell, \Delta, \mathrm{none}, \mathrm{lst};\ \rho)`$ の最初の項を $`I`$ に足す。ここで $`e = \mathrm{root}(b + \Sigma(I))`$（枠）とし、$`e`$ を $`x`$ の下に記録する。
  - (F-4-1) もし $`e`$ が $`\le_2`$ になりうるならば、ここで $`W'`$ をその最後の子とし、$`\mathrm{root}(\mathrm{ch}(e) \text{ から } W' \text{ を除いたもの},\ W'')`$ も $`x`$ の下に記録する。ここで $`W''`$ は $`W'`$ から単位の子を除いたもの（入れ子の土台）である。

  そして $`S = S \oplus e`$ とする。
- (F-5) そうでなければ：
  - (F-5-1) もし $`y(c) \ge 1`$ ならば、$`S = S \oplus \mathrm{C2}_x(c;\ \ell, (), \mathrm{lst};\ \rho)`$ とする。
  - (F-5-2) そうでなければ、$`S = S \oplus \mathrm{root}(\mathrm{ch}(c))`$ とする。

結果は $`S`$ である。

<a id="a12"></a>
### A.12 $`U`$ の加数：極限、覆う、組、塊（D5）

これらの関数は、$`\omega`$ の列 $`G`$、$`G'`$（$`U`$ の形の加数、A.3）を取って真偽、並び、列を返す。$`\mathrm{blk}`$ は (lh-3-3-1) から、$`\mathrm{grp}`$ は $`\mathrm{blk}`$ と $`\mathrm{wit}`$（A.4）から、他は $`\mathrm{grp}`$、$`\mathrm{wit}`$、LG（A.9）、(F-2) から呼ばれる。

**塊。** $`\mathrm{blk}(U)`$ は、前の極限の加数が塊を持つことを表す。$`G = \mathrm{ch}(U)`$ の最後の組を $`(a, b)`$ とするとき、$`i \lt a`$ のある $`G_i`$ が $`\mathrm{lim}(G_i)`$ かつ $`\mathrm{cont}(G_i)`$ を満たすときに真である。

**組。** $`\mathrm{grp}(G_1, \ldots, G_n)`$ は番号の対 $`(i, j)`$ の並びである（1 つの対が 1 つの組を表す）。$`i = 1`$ から始める。$`i \le n`$ の間、$`j = i`$ として：
- (grp-1) もし $`\mathrm{lim}(G_j)`$、$`j \lt n`$、$`\mathrm{ch}(G_{j+1}) = ()`$ ならば、$`j = j + 1`$ とする。
- (grp-2) そうでなく、もし $`\mathrm{lim}(G_j)`$、$`j \lt n`$、$`\mathrm{lvonly}(G_{j+1})`$ ならば、$`j = j + 1`$ とする。
- (grp-3) そうでなく、もし $`\mathrm{lim}(G_j)`$、$`j \lt n`$、$`\mathrm{cov}(G_j, G_{j+1})`$ ならば、$`j = j + 1`$ とする。

そして $`(i, j)`$ を並びに足し、$`i = j + 1`$ とする。**最後の組**は最後の対 $`(a, b)`$ であり、$`b = n`$ である。

**極限の加数。** $`\mathrm{lim}(G)`$ は、$`G`$ の一番右の葉が $`G`$ の印であることを表す。一番右の道を $`\pi_0 = G, \pi_1, \ldots, \pi_r`$ とする（$`\pi_{i+1}`$ は $`\pi_i`$ の最後の子、$`\pi_r`$ は子を持たない）。$`f = \pi_r`$ とする。
- (lim-1) もし $`r = 0`$、$`z(f) \ne 0`$、$`y(f) \lt 1`$ のどれかならば、$`\mathrm{lim}(G)`$ は偽である。
- (lim-2) そうでなければ、$`i = r - 1, r - 2, \ldots, 0`$ の順に見る。もし $`z(\pi_i) = 1`$ かつ $`y(\pi_i) \le y(f)`$ ならば：
  - (lim-2-1) もし $`i \ne 0`$ かつ $`y(\pi_i) = y(G) = y(f)`$ ならば、次の $`i`$ へ進む（$`G`$ と同じ段の $`\omega`$ の子は通り抜ける）。
  - (lim-2-2) そうでなければ、$`\mathrm{lim}(G)`$ は、$`i = 0`$ かつ $`y(G) = y(f)`$ のときに真である。
- (lim-3) もし結果が出ないまま見終わったならば、$`\mathrm{lim}(G)`$ は偽である。

**段だけ。** $`\mathrm{lvonly}(G)`$ は、$`G`$ のどの子 $`c`$ も $`G`$ の 1 段上の子で $`\mathrm{lvonly}(c)`$ を満たすときに真である（子が無ければ真）。

**覆う。** $`\mathrm{cov}(G, G')`$ は、極限の加数 $`G`$ の後の加数 $`G'`$ が $`G`$（またはその子の頭の部分で、$`G`$ の段が覆われるもの）を繰り返すことを表す。
- (cov-1) もし $`\mathrm{cont}(G)`$（下）かつ $`\mathrm{ch}(G) \ne ()`$ ならば：ここで $`C = \mathrm{ch}(G')`$ とする。
  - (cov-1-1) もし $`C \ne ()`$ で、その最後の成分が $`1`$ で、$`|C| \ge 2`$ で、$`\mathrm{em}(C_{|C|-1}, y(G'))`$ ならば、$`C`$ の最後の成分を除く。
  - (cov-1-2) もし $`C \ne ()`$、$`|C| \lt |\mathrm{ch}(G)|`$、$`C`$ が $`\mathrm{ch}(G)`$ の頭の部分、$`|L(G)| \le |L((y(G'), z(G'), C))|`$（A.8）ならば、$`\mathrm{cov}(G, G')`$ は真である。

  ここで真にならなければ、(cov-2) へ進む。
- (cov-2) もし $`\mathrm{cont}(G)`$ が偽、$`\mathrm{ch}(G) = ()`$、$`G`$ の最後の子が $`(y(G), 0, ())`$ でない、のどれかならば、偽である。
- (cov-3) ここで $`s = \mathrm{strip}(G)`$ とする。もし $`s = \mathrm{none}`$ か $`\mathrm{ch}(s) = ()`$ ならば、偽である。
- (cov-4) もし $`G' = s`$ ならば、真である。
- (cov-5) そうでなければ、次がすべて成り立つときに真である。$`\mathrm{ch}(G') \ne ()`$、$`G'`$ の最後の子が $`1`$、$`|\mathrm{ch}(G')| \ge 2`$、その前の子と $`y(G')`$ で $`\mathrm{em}`$ が成り立つ、$`G'`$ から最後の子を除いたものが $`s`$ に等しい。

**葉を取る。** $`\mathrm{strip}(G)`$ は一番右の葉を除く。
- (strip-1) もし $`\mathrm{ch}(G) = ()`$ ならば、結果は $`\mathrm{none}`$ である。
- (strip-2) そうでなければ、ここで $`s'`$ を最後の子 $`B_k`$ の $`\mathrm{strip}`$ とする。結果は $`(y(G), z(G), (B_1, \ldots, B_{k-1}))`$ である。ただし $`s' \ne \mathrm{none}`$ なら最後に $`s'`$ を足す。

**印で終わる。** $`\mathrm{em}(K, \ell)`$ は、$`K`$ の一番右の葉 $`f`$（最後の子をたどって着く。$`K`$ が子を持たなければ $`f = K`$）が $`z(f) = 0`$ かつ $`y(f) = \ell`$ のときに真である。

**中身。** $`\mathrm{cont}(G)`$ は、$`G`$ のある段の列が鎖以外の子を持つことを表す。
- (cont-1) もし $`\mathrm{up}(G) = ()`$ ならば、偽である。
- (cont-2) そうでなければ、$`\mathrm{sub}^\top(G)`$（A.7）の最初以外のある成分 $`C`$ が $`\mathrm{Rest}(C) \ne ()`$ を満たすときに真である。

**印を置き換える。** $`\mathrm{limx}(G, x)`$ は、$`G`$ の一番右の葉を根の項 $`x`$ に置き換える。
- (limx-1) もし $`\mathrm{ch}(G) = ()`$ ならば、結果は $`\mathrm{root}(\mathrm{ch}(x)) = x`$ である。
- (limx-2) そうでなければ、結果は $`(y(G), z(G), (B_1, \ldots, B_{k-1}, \mathrm{limx}(B_k, x)))`$ である。

**段だけの鎖。** $`k \gt 1`$ なら $`\mathrm{lchain}(y, k) = (y, 1, (\mathrm{lchain}(y + 1, k - 1)))`$、$`k \le 1`$ なら $`(y, 1, ())`$ とする。

<a id="a13"></a>
### A.13 畳み込み $`\oplus`$（D9）

$`S \oplus Y`$ は、最初の項が $`S_1`$ の空でない和 $`S`$ と項 $`Y`$ を取って和を返し、$`\mathrm{lh}`$（A.2）、$`\mathrm{lh}_1`$ と LG（A.9）、F（A.11）から呼ばれる。
- (fold-1) もし $`Y \le S_1`$ ならば、結果は $`S + (Y)`$ である。
- (fold-2) もし $`Y \gt S_1`$ で $`Y`$ が $`\le_2`$ になりうるならば、結果は $`\mathrm{lh}(Y) + (Y)`$ である。
- (fold-3) そうでなければ、結果は $`\mathrm{lh}(Y)`$ である。

$`S \succ S'`$ は 2 つの和を項ごとに比べる。項が違う最初の位置で、大きい項の方が大きい。一方が他方の頭の部分なら、長い方が大きい。

<a id="a14"></a>
### A.14 根の $`\omega`$ の並びのコピー（D4）

$`\mathrm{Up}(a;\ N, \mathrm{last})`$ は、根の $`\omega`$ の列 $`a`$、根の項 $`N`$、旗を取り、$`a`$ を 1 段上げた列を返し、(lh-5) から呼ばれる。$`r(s, Y, \mathrm{lst})`$ を使う。ここで $`s = (y, z, B)`$ は列、$`Y`$ は段の並び（$`s`$ より上の $`\omega`$ の列の段）、$`\mathrm{lst}`$ は旗である。
- (Up-1) もし $`y = 0`$ ならば、$`r = s`$ である。
- (Up-2) もし $`\mathrm{lst}`$、$`B = ()`$、$`z = 0`$、$`N \ne \mathrm{none}`$ ならば：ここで $`Y'`$ を、$`Y`$ の成分 $`o`$ のうち $`o \le y`$ のものを順に並べたものとする。もし $`Y' \ne ()`$ で、（$`|Y'| = 1`$、または $`Y'`$ の成分がすべて $`y`$ で $`\max Y \gt y`$）であり、$`Y'`$ の最後の成分が $`y`$ で、$`Y_1 = y`$ ならば、$`r = N`$ である（最後の印は $`\Omega_1`$ 倍の $`N`$ である）。この条件が成り立たなければ、(Up-3) へ進む。
- (Up-3) そうでなければ、$`z = 1`$ なら $`Y'' = (Y, y)`$、そうでなければ $`Y'' = Y`$ とする。$`r = (y + 1,\ z,\ (r(B_1, Y'', \mathrm{lst} \land 1 = k), \ldots, r(B_k, Y'', \mathrm{lst} \land k = k)))`$ である。旗は最後の子だけに渡る。

$`\mathrm{ch}(a) = (B_1, \ldots, B_k)`$ に対して、$`\mathrm{Up}(a;\ N, \mathrm{last}) = (2,\ 1,\ (r(B_i, (y(a)), \mathrm{last} \land i = k))_{i = 1, \ldots, k})`$ とする。

<a id="a15"></a>
### A.15 列を分ける（D1）

これら 3 つの関数は、列か列の並びを取って列の並びか列を返し、(le2-3)、(lh-7)、(lh-8) から呼ばれる。
- $`\mathrm{split}(W) = (\mathrm{hi}, \mathrm{lo})`$：$`\mathrm{hi}`$ は $`W`$ の子のうち $`y \ge 2`$ か $`z = 1`$ のもの、
  $`\mathrm{lo}`$ は残りである（どちらも順のまま）。
- $`\Omega\mathrm{pre}(\mathrm{hi})`$ は、$`\mathrm{hi}`$ の頭の部分で、列がすべて $`z = 1`$ である一番長いものである。
- $`W + k = (y(W), z(W), (\mathrm{ch}(W), 1^k))`$：子の後ろに単位を $`k`$ 個足す。

<a id="a16"></a>
### A.16 潰す操作 C1（D2）

$`\mathrm{C1}_N`$ は根の項 $`N`$ の上で列を潰して項か包んだ列を返し、$`\mathrm{C1s}_N`$ は並びの上で同じことをして和を返し、$`\mathrm{c1fixed}`$ は並びを調べ、これらは (le2-4)、(lh-7)、(lh-8)、(lh-8-3)、(C2-5-3) から呼ばれる。

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

**持ち主を探す。** $`\mathrm{own}(\sigma, y)`$ は、成分の積み重ね $`\sigma`$ と段 $`y`$ を取る。成分は
$`(y_e, h_e)`$ か $`(y_e, h_e, \mathrm{ok}_e)`$ である。$`\omega`$ の列の段、その像のずれ、（C1 では）旗を表す。
$`y_a \le y`$ となる一番上の成分を $`a`$ とする。
- (own-1) もし $`a`$ があり、3 つ目の成分を持ち、$`\mathrm{ok}_a`$ が偽ならば、結果は $`\mathrm{none}`$ である。
- (own-2) もし $`a`$ があり、それ以外ならば、結果は $`a`$ である。
- (own-3) もし $`y_a \le y`$ の成分が無いならば、結果は $`\mathrm{none}`$ である。

<a id="a17"></a>
### A.17 同じ段の $`\omega`$ の列の読み（D3）

$`\mathrm{Kimg}`$ は同じ段の $`\omega`$ の列 $`K`$ を取ってその加数（根の項）を返し、$`\mathrm{KI}`$ はそのような列の子を取ってその読み（和）を返し、2 つは互いに呼び合い、LK（A.10）、F（A.11）、(C2-2)、(C2-3)（A.18）から呼ばれる。段の並び $`\Delta`$ と読みの文脈 $`\rho`$ は[記法](#level-list)にある。

$`\mathrm{Kimg}(K;\ x, \ell, \Delta, t_0, \mathrm{last}, c, j_0;\ \rho)`$ は、$`y(K) = \ell`$ の同じ段の $`\omega`$ の列 $`K`$ の加数である。$`c`$ は上限（$`\mathrm{none}`$ か整数。与えられなければ $`\mathrm{none}`$）、$`j_0`$ は旗（与えられなければ $`\mathrm{false}`$）である。結果は根の項である。
- (Kimg-1) もし $`\Delta = (\Delta_1, \ldots, \Delta_n)`$ が並びならば：ここで $`B = \mathrm{ch}(K)`$、$`j = \min(\mathrm{lev}(K) - 1,\ n - 1)`$（A.8）、$`V = \mathrm{up}(K)`$ とする。$`\kappa`$（$`K`$ が共有しうる段の列）を次のように定める。
  - (Kimg-1-1) もし $`\rho_1 = (d, \kappa')`$ かつ $`d = x`$ ならば、$`\kappa = \kappa'`$ である。
  - (Kimg-1-2) そうでなく、もし $`x \ne \mathrm{none}`$ で $`x`$ が $`\le_2`$ になりうるならば、$`\kappa = K_1(x)`$（下）である。
  - (Kimg-1-3) そうでなければ、$`\kappa = \mathrm{none}`$ である。

  次に：
  - (Kimg-1-4) もし $`V \ne ()`$、$`\kappa \ne \mathrm{none}`$、$`V_1 = \kappa`$、$`\mathrm{Rest}(V_1) \ne ()`$ ならば（`kbcut`：$`K`$ は $`K_1`$ の段を共有する）、子 $`V_1`$ を $`B`$ から除き、$`j = \min(|V| - 1,\ n - 1)`$ とする。
    - (Kimg-1-4-1) もし $`c \ne \mathrm{none}`$ ならば、$`j = \max(0, \min(j, c))`$ とする（`kb2`）。

    そして子 $`V_2, \ldots, V_{1+j}`$ を $`B`$ から除く。
  - (Kimg-1-5) そうでなく、もし $`j \ne 0`$ か $`V \ne ()`$ ならば、$`K`$ の 1 段上の子をすべて $`B`$ から除く。
  - (Kimg-1-6) もし $`j_0`$ ならば（**規則 `kdl0`**）：ここで $`\Lambda = L(K)`$（A.8）とし、$`j`$ を $`\Lambda_i \ne \bot`$ かつ項として $`\Lambda_i = \Lambda_1`$ となる一番大きい $`i - 1`$（無ければ $`0`$）とし、$`j = \min(j, n - 1)`$ とし、$`B`$ を $`\mathrm{ch}(K)`$ から 1 段上の子を除いたものとする。理由：年上の兄弟の後に読む（または同じ段の子の中に入れ子になった）$`D`$ の段の $`\omega`$ の列は、その最後の鎖の一番下の段で読み、その一番上より上では読まない。

  結果は $`\mathrm{root}(\Delta_{1+j} + \mathrm{KI}(B;\ x, \ell, \Delta, t_0', \mathrm{last};\ \rho))`$ である。ここで $`\mathrm{last}`$ なら $`t_0' = t_0`$、そうでなければ $`t_0' = \mathrm{none}`$ とする。
- (Kimg-2) そうでなければ（$`\Delta = b`$ は 1 つの土台）、結果は $`\mathrm{root}(b + \mathrm{KI}(\mathrm{ch}(K);\ x, \ell, b, t_0', \mathrm{last};\ \rho))`$ である。$`t_0'`$ は上と同じである。

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

$`\le_2`$ になりうる $`x`$ に対して、$`K_1(x)`$ はその列 $`D`$（A.3）の最初の 1 段上の子である。$`D`$ が 1 段上の子を持たなければ $`\mathrm{none}`$ である。

<a id="a18"></a>
### A.18 潰す操作 C2（D3）

$`\mathrm{C2}_x`$ は $`\omega`$ の列の中で読む列を行き先 $`x`$ へ潰して項を返し、$`\mathrm{C2s}_x`$ は並びの上で同じことをして和を返し、これらは (OL-1-2)、(F-5-1)、KI（A.17）から呼ばれる。

$`\mathrm{C2}_x`$ は $`\Omega_\omega \mapsto x`$、$`\Omega_{\omega+j} \mapsto \Omega_j`$ である。どの印も、それを持つ $`\omega`$ の列の行き先へ潰れる。

$`\mathrm{C2}_x(s;\ \ell, \sigma, \mathrm{last};\ \rho)`$ は、根の項 $`x`$（行き先）、列 $`s = (y, z, B)`$、潰している $`\omega`$ の列 $`D`$ の段 $`\ell`$、成分 $`(y_e, h_e)`$ の積み重ね $`\sigma`$、旗、文脈を取る。結果は項である。
- (C2-1) もし $`y = 0`$ ならば、結果は $`s`$ である。
- (C2-2) もし $`z = 1`$、$`\rho_D = (x', \ell')`$、$`y = \ell'`$、$`y \lt \ell`$ ならば（段の列の奥にある $`D`$ の段の $`\omega`$ の列）：ここで $`\rho'`$ を、$`\rho`$ の $`\rho_D`$ を $`\mathrm{none}`$ に置き換えたものとする。
  - (C2-2-1) もし $`x'`$ が $`\le_2`$ になりうり（A.3、その $`U'`$、$`q'`$、最後の $`\omega`$ の列 $`D'`$）、かつ $`\mathrm{kdl}(D', L(D')) = s`$（A.8）ならば、結果は $`\mathrm{Kimg}(s;\ x', \ell', (\delta'_1, \ldots, \delta'_{q'}), \mathrm{none}, \mathrm{last}, \mathrm{none}, \mathrm{true};\ \rho')`$ である。ここで $`\delta'_i = (\mathrm{ch}(x'), U'^i)`$ とする。
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

<a id="notation"></a>
### 付録：記法

**項、和、場所。**

- **項**は $`s = (y, z, B)`$ である。$`y = y(s)`$ は列の行 1 の成分（**段**）、$`z = z(s)`$ は行 2 の成分、
  $`B = \mathrm{ch}(s) = (B_1, \ldots, B_k)`$ は順に並んだ子である。行 0 の成分は木の深さであり、
  持たない。
- $`1 = (0, 0, ())`$ は行列 $`(0,0,0)`$ である。$`1`$ に等しい子を**単位**と呼ぶ。
- **和**は項の有限列 $`(t_1, \ldots, t_n)`$ である。$`()`$ は $`0`$ である。列 $`B`$ に対して
  $`\mathrm{root}(B) = (0, 0, B)`$ とする。
- $`(A, B)`$ は列 $`A`$ と $`B`$ をつないだもの、$`U^m`$ は $`U`$ を $`m`$ 個並べた列である。よって
  $`\mathrm{root}(A, U^m)`$ は、子が $`A`$ と $`m`$ 個の $`U`$ である根の項である。$`A + B`$ はいつも A.5 の和で
  あり、つなぐことではない。
- 列は木の中の場所である。「最初の 1 段上の子」「最後の子」「並びの成分である」などの言葉は場所を指す。
  $`=`$ は項として比べる。別の場所にある等しい 2 つの列は、別の列である。
- 並びの番号は 1 から数える。$`\bot`$ は「列が無い」を表す並びの成分、$`\mathrm{none}`$ は値が無いことを表す。
- 列 $`K`$ に対して：
  - $`K`$ の **1 段上の子**とは、$`z(c) = 1`$ かつ $`y(c) = y(K) + 1`$ の子 $`c`$ である。$`\mathrm{up}(K)`$ は
    それらを順に並べたものである。
  - $`\mathrm{Rest}(K)`$ は、$`K`$ の他の子を順に並べたものである。
  - $`K`$ の**同じ段の子**とは、$`z(c) = 1`$ かつ $`y(c) = y(K)`$ の子 $`c`$ である。

<a id="read-context"></a>
**読みの文脈。** 潰す操作 C2 と、同じ段の $`\omega`$ の列の読み（A.18、A.17）は、**読みの文脈** $`\rho = (\rho_C, \rho_D, \rho_1)`$ を取る。どの部分も $`\mathrm{none}`$ か、次のものである。
- $`\rho_C = (c, \ell_C, \Delta_C)`$：読んでいる $`\omega`$ の列は節点 $`c`$ に属し、段は $`\ell_C`$、段の並びは $`\Delta_C`$ である（下）。
- $`\rho_D = (x', \ell')`$：$`\le_2`$ になりうる節点 $`x'`$ の段の列を読んでいる。$`\ell'`$ はその列 $`D`$ の段である（A.3）。
- $`\rho_1 = (d, \kappa)`$：読みは後者 $`d`$ に属し、$`\kappa`$ は次の段の列（または $`\mathrm{none}`$）である。

分岐が特に言わない限り、文脈はそのまま下へ渡す。**$`\mathrm{lh}`$（A.2）の計算は、どれも空の文脈 $`\rho_\varnothing = (\mathrm{none}, \mathrm{none}, \mathrm{none})`$ から始める。** 別の計算の中から呼ばれたときも同じである。

<a id="level-list"></a>
**段の並び。** **段の並び** $`\Delta`$ は、子の並びの並び $`(\Delta_1, \ldots, \Delta_n)`$（A.3 の段 $`\delta_m = \mathrm{ch}(d_m)`$）か、**1 つの土台** $`b`$（子の並び 1 つ）である。

**分岐の書き方。** 操作は分岐の入れ子の箇条書きで書く。各節は、入力、出力、その操作を呼ぶところを述べる文で始まる。次に、分岐をコードと同じ順に並べ、(C2-5-1) のようなラベルを付ける。ラベルは関数の名前で始まるので、1 つの関数のラベルは 1 つの並びになる。「そうでなければ」は、いつも「同じ深さの前の分岐のどれにも当てはまらないならば」の意味である。

<a id="names"></a>
### 付録：コードの中の名前

| 本文 | `phi3def2.py` | 本文 | `phi3def2.py` |
|---|---|---|---|
| $`\mathrm{eps}`$, $`\log`$, $`\lambda`$ | `is_eps`, `log0`, `lam` | $`\mathrm{own}`$ | `_nearest` |
| $`\mathrm{split}`$, $`\Omega\mathrm{pre}`$, $`W + k`$ | `split`, `omega_prefix`, `plus` | $`\mathrm{C1}`$, $`\mathrm{C1s}`$, $`\mathrm{c1fixed}`$ | `C1`, `C1s`, `c1fixed` |
| $`\mathrm{C2}`$, $`\mathrm{C2s}`$ | `C2`, `C2s` | $`\rho_C`$, $`\rho_D`$, $`\rho_1`$ | `KCTX`, `KDX`, `K1REF` |
| $`\mathrm{KI}`$, $`\mathrm{Kimg}`$ | `KI`, `Kimg` | $`K_1(x)`$, $`\mathrm{shares}`$ | `k1_of`, `shares_k1` |
| $`\mathrm{Up}`$ | `Up` | $`\mathrm{lim}`$, $`\mathrm{lvonly}`$, $`\mathrm{strip}`$ | `is_limit`, `levels_only`, `strip_marker` |
| $`\mathrm{cov}`$, $`\mathrm{grp}`$, $`\mathrm{cont}`$ | `covers`, `groups`, `has_content` | $`\mathrm{limx}`$, $`\mathrm{lchain}`$, $`\mathrm{blk}`$ | `limx`, `lchain`, `has_block` |
| $`\mathrm{Rest}`$, $`\mathrm{cut}`$ | `k2kids(K, 'all')`, `k2kids(K, 'cut')` | $`\mathrm{sub}`$, $`\mathrm{sub}^\top`$ | `subcols(K)`, `subcols(K, top=True)` |
| $`L`$, $`\mathrm{kdl}`$, $`\mathrm{ins}`$ | `level_cols`, `kdl_nested`, `kdl2_insert` | $`\mathrm{lev}`$, $`\mathrm{lev} - 1`$, $`\mathrm{chtop}`$ | `zsib`（= `zdepth`）, `zlead`, `chtop_col` |
| $`\mathrm{le2}`$, $`\mathrm{succ}`$, $`\mathrm{dead}`$, $`\mathrm{d1}`$ | `le2_info`, `le2_succ`, `is_dead`, `d1_info` | $`\mathrm{Img}`$, $`\mathrm{pre}`$ | `IDXIMG`, `PREBLOCK` |
| $`\mathrm{LK}`$, $`\mathrm{OL}`$, $`\mathrm{OD}`$, $`\mathrm{em}`$ | `level_kids`, `ownleaf`, `owndeep`, `ends_in_marker` | $`\mathrm{F}`$ | `_lh1_kids` |
| $`\oplus`$, $`\succ`$ | `oplus`, `scmp` | $`\mathrm{lh}`$, $`\mathrm{lh}_1`$, $`\mathrm{LG}`$ | `lh`, `lh1_le2`, `_lh1_groups` |
| $`\mathrm{wit}`$, $`\mathrm{cl}`$, $`\mathrm{copy}`$ | `le2_wit`, `closure`, `d94_copy` | $`\Phi_3`$, 出力 | `build`, `pattern`, `show` |
| $`\mathrm{parse}`$, $`\mathrm{tree}`$ | `tss.parse`, `tss.from_mat` | $`\mathrm{cols}`$, $`\mathrm{mat}`$, $`+`$, $`\Sigma`$ | `tss.cols_term`, `tss.mat`, `tss.add`, `tss.addall` |

**コードについての注。** 読みの文脈は大域の積み重ね（`KCTX`、`KDX`、`K1REF`）に置かれ、入れ子の `lh` の呼び出しはそれを空にしない。3290 個の試験の行列すべてで、`lh` を呼ぶたびにそれらを空にしても同じパターンになる。よって本文は空にする形（[記法](#read-context)）で書いた。`C2` と `C2s` の引数 `top` は何もしない。
