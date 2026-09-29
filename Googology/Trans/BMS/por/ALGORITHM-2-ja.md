[← 戻る](README-ja.md) | [English](ALGORITHM-2.md) | [Japanese](ALGORITHM-2-ja.md)

# トリオ数列をパターンに変換する：アルゴリズムの後半

これは `phi3def2.py` のアルゴリズムの 2 つ目の部分である。1 つ目の部分（使い方、約束、A.1–A.8）は
[README-ja.md](README-ja.md) にある。

### A.9 $`U`$ の加数：極限、覆う、組、塊（D5）

ここで $`G`$、$`G'`$ は $`\omega`$ の列（$`U`$ の形の加数、A.13）である。

**極限の加数。** $`\mathrm{lim}(G)`$ は、$`G`$ の一番右の葉が $`G`$ の印であることを表す。一番右の道を $`\pi_0 = G, \pi_1, \ldots, \pi_r`$ とする（$`\pi_{i+1}`$ は $`\pi_i`$ の最後の子、$`\pi_r`$ は子を持たない）。$`f = \pi_r`$ とする。
- (lim-1) もし $`r = 0`$、$`z(f) \ne 0`$、$`y(f) \lt 1`$ のどれかならば、$`\mathrm{lim}(G)`$ は偽である。
- (lim-2) そうでなければ、$`i = r - 1, r - 2, \ldots, 0`$ の順に見る。もし $`z(\pi_i) = 1`$ かつ $`y(\pi_i) \le y(f)`$ ならば：
  - (lim-2-1) もし $`i \ne 0`$ かつ $`y(\pi_i) = y(G) = y(f)`$ ならば、次の $`i`$ へ進む（$`G`$ と同じ段の $`\omega`$ の子は通り抜ける）。
  - (lim-2-2) そうでなければ、$`\mathrm{lim}(G)`$ は、$`i = 0`$ かつ $`y(G) = y(f)`$ のときに真である。
- (lim-3) もし結果が出ないまま見終わったならば、$`\mathrm{lim}(G)`$ は偽である。

**段だけ。** $`\mathrm{lvonly}(G)`$ は、$`G`$ のどの子 $`c`$ も $`G`$ の 1 段上の子で $`\mathrm{lvonly}(c)`$ を満たすときに真である（子が無ければ真）。

**葉を取る。** $`\mathrm{strip}(G)`$ は一番右の葉を除く。
- (strip-1) もし $`\mathrm{ch}(G) = ()`$ ならば、結果は $`\mathrm{none}`$ である。
- (strip-2) そうでなければ、ここで $`s'`$ を最後の子 $`B_k`$ の $`\mathrm{strip}`$ とする。結果は $`(y(G), z(G), (B_1, \ldots, B_{k-1}))`$ である。ただし $`s' \ne \mathrm{none}`$ なら最後に $`s'`$ を足す。

**印で終わる。** $`\mathrm{em}(K, \ell)`$ は、$`K`$ の一番右の葉 $`f`$（最後の子をたどって着く。$`K`$ が子を持たなければ $`f = K`$）が $`z(f) = 0`$ かつ $`y(f) = \ell`$ のときに真である。

**覆う。** $`\mathrm{cov}(G, G')`$ は、極限の加数 $`G`$ の後の加数 $`G'`$ が $`G`$（またはその子の頭の部分で、$`G`$ の段が覆われるもの）を繰り返すことを表す。
- (cov-1) もし $`\mathrm{cont}(G)`$（下）かつ $`\mathrm{ch}(G) \ne ()`$ ならば：ここで $`C = \mathrm{ch}(G')`$ とする。
  - (cov-1-1) もし $`C \ne ()`$ で、その最後の成分が $`1`$ で、$`|C| \ge 2`$ で、$`\mathrm{em}(C_{|C|-1}, y(G'))`$ ならば、$`C`$ の最後の成分を除く。
  - (cov-1-2) もし $`C \ne ()`$、$`|C| \lt |\mathrm{ch}(G)|`$、$`C`$ が $`\mathrm{ch}(G)`$ の頭の部分、$`|L(G)| \le |L((y(G'), z(G'), C))|`$（A.11）ならば、$`\mathrm{cov}(G, G')`$ は真である。

  ここで真にならなければ、(cov-2) へ進む。
- (cov-2) もし $`\mathrm{cont}(G)`$ が偽、$`\mathrm{ch}(G) = ()`$、$`G`$ の最後の子が $`(y(G), 0, ())`$ でない、のどれかならば、偽である。
- (cov-3) ここで $`s = \mathrm{strip}(G)`$ とする。もし $`s = \mathrm{none}`$ か $`\mathrm{ch}(s) = ()`$ ならば、偽である。
- (cov-4) もし $`G' = s`$ ならば、真である。
- (cov-5) そうでなければ、次がすべて成り立つときに真である。$`\mathrm{ch}(G') \ne ()`$、$`G'`$ の最後の子が $`1`$、$`|\mathrm{ch}(G')| \ge 2`$、その前の子と $`y(G')`$ で $`\mathrm{em}`$ が成り立つ、$`G'`$ から最後の子を除いたものが $`s`$ に等しい。

**組。** $`\mathrm{grp}(G_1, \ldots, G_n)`$ は番号の対 $`(i, j)`$ の並びである（1 つの対が 1 つの組を表す）。$`i = 1`$ から始める。$`i \le n`$ の間、$`j = i`$ として：
- (grp-1) もし $`\mathrm{lim}(G_j)`$、$`j \lt n`$、$`\mathrm{ch}(G_{j+1}) = ()`$ ならば、$`j = j + 1`$ とする。
- (grp-2) そうでなく、もし $`\mathrm{lim}(G_j)`$、$`j \lt n`$、$`\mathrm{lvonly}(G_{j+1})`$ ならば、$`j = j + 1`$ とする。
- (grp-3) そうでなく、もし $`\mathrm{lim}(G_j)`$、$`j \lt n`$、$`\mathrm{cov}(G_j, G_{j+1})`$ ならば、$`j = j + 1`$ とする。

そして $`(i, j)`$ を並びに足し、$`i = j + 1`$ とする。**最後の組**は最後の対 $`(a, b)`$ であり、$`b = n`$ である。

**中身。** $`\mathrm{cont}(G)`$ は、$`G`$ のある段の列が鎖以外の子を持つことを表す。
- (cont-1) もし $`\mathrm{up}(G) = ()`$ ならば、偽である。
- (cont-2) そうでなければ、$`\mathrm{sub}^\top(G)`$（A.10）の最初以外のある成分 $`C`$ が $`\mathrm{Rest}(C) \ne ()`$ を満たすときに真である。

**印を置き換える。** $`\mathrm{limx}(G, x)`$ は、$`G`$ の一番右の葉を根の項 $`x`$ に置き換える。
- (limx-1) もし $`\mathrm{ch}(G) = ()`$ ならば、結果は $`\mathrm{root}(\mathrm{ch}(x)) = x`$ である。
- (limx-2) そうでなければ、結果は $`(y(G), z(G), (B_1, \ldots, B_{k-1}, \mathrm{limx}(B_k, x)))`$ である。

**段だけの鎖。** $`k \gt 1`$ なら $`\mathrm{lchain}(y, k) = (y, 1, (\mathrm{lchain}(y + 1, k - 1)))`$、$`k \le 1`$ なら $`(y, 1, ())`$ とする。

**塊。** $`\mathrm{blk}(U)`$ は、前の極限の加数が塊を持つことを表す。$`G = \mathrm{ch}(U)`$ の最後の組を $`(a, b)`$ とするとき、$`i \lt a`$ のある $`G_i`$ が $`\mathrm{lim}(G_i)`$ かつ $`\mathrm{cont}(G_i)`$ を満たすときに真である。

### A.10 切れた列と鎖（D6）

**切れる。** $`\mathrm{cut}(K)`$ は、$`K`$ の鎖を終わらせる子の並びである。
- (cut-1) もし $`K`$ が同じ段の子を持つならば、$`\mathrm{cut}(K) = ()`$ である。
- (cut-2) もし $`K`$ が $`z(c) = 0`$ かつ $`y(c) \gt y(K)`$ の子 $`c`$（添字の列）を持つならば、$`\mathrm{cut}(K) = ()`$ である。
- (cut-3) そうでなければ、$`\mathrm{cut}(K)`$ は、$`c \in \mathrm{Rest}(K)`$ のうち（$`z(c) = 0`$ かつ $`y(c) \le y(K)`$）か $`y(c) \lt y(K)`$ のものの並びである。

$`K`$ が**切れている**とは、$`\mathrm{cut}(K) \ne ()`$ のことである。

**鎖。** $`\mathrm{sub}(K)`$ と $`\mathrm{sub}^\top(K)`$ は、列と、その上の段の列の並びである。違いは (sub-2-2) だけである。下の再帰の呼び出しは、$`\mathrm{sub}^\top`$ の中でも、すべて $`\mathrm{sub}`$ である。ここで $`V = \mathrm{up}(K)`$ とする。
- (sub-1) もし $`V = ()`$ ならば、結果は $`(K)`$ である。
- (sub-2) そうでなければ、ここで $`H = \mathrm{sub}(V_1)`$ とし、$`H`$ の最後の成分が切れているとき真となる旗を $`\gamma`$ とする。$`(K, H)`$ から始める。$`V_2, V_3, \ldots`$ の各 $`S`$ について：
  - (sub-2-1) もし $`S = V_1`$ か $`\gamma`$ ならば、$`\mathrm{sub}(S)`$ を足す。

  次に：
  - (sub-2-2) $`\mathrm{sub}`$ だけで（$`\mathrm{sub}^\top`$ では行わない）、かつ $`\gamma`$ が偽のときだけ：ここで $`E`$ を、$`V_2, V_3, \ldots`$ のうち $`S \ne V_1`$ のものの並びとする。もし $`E \ne ()`$ で、「$`|E| = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$」でないならば、各 $`E_i`$ について：
    - (sub-2-2-1) もし $`i = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$ ならば、飛ばす。
    - (sub-2-2-2) そうでなければ、$`\mathrm{sub}(E_i)`$ を足す。

### A.11 段の列 $`L(D)`$（D6）

$`L(D)`$ は $`\omega`$ の列 $`D`$ の段の列の並びである。$`\le_2`$ の後者 $`d_m`$（A.13）1 つに 1 つの成分が対応し、列の無い段は $`\bot`$ である。ここで $`V = \mathrm{up}(D)`$ とする。
- (L-1) もし $`V = ()`$ ならば、$`L(D) = (\bot)`$ である。
- (L-2) そうでなければ、ここで $`F = \mathrm{sub}(V_1)`$（最初の鎖）、$`C`$ を $`\mathrm{sub}^\top(D)`$ から最初の成分 $`D`$ を除いたもの、$`Q`$ を $`D`$ の同じ段の子の並びとする。まず**一番下の段**を置く。
  - (L-2-1) もし $`Q \ne ()`$ で、$`C`$ のある成分 $`c`$ が $`\mathrm{Rest}(c) \ne ()`$ を満たし、「$`Q_1`$ が 1 段上の子を持ち、その最初のものが $`V_1`$ に等しい」でないならば：もし $`\mathrm{up}(Q_1) = ()`$ ならば $`C = (\bot, C)`$ とする（L-2-1-1）。そうでなければ $`C = (L(Q_1), C)`$ とする（L-2-1-2）。
  - (L-2-2) そうでなく、もし $`C`$ のある成分 $`c`$ に、$`z(g) = 1`$、$`y(g) = y(D)`$、$`\mathrm{shares}(g, V_1)`$ が偽の $`g \in \mathrm{Rest}(c)`$ があるならば：ここで $`K'`$ をそのような最初の $`g`$（$`c`$ の順、次に $`g`$ の順）とし、$`C = (L(K'), C)`$ とする。
  - (L-2-3) そうでなく、もし $`\mathrm{kdl}(D, C) \ne \mathrm{none}`$（下）ならば、$`C = (L(\mathrm{kdl}(D, C)), C)`$ とする。

  次に $`C = \mathrm{ins}(C)`$（下）とする。次に**自分の一番上の段**を入れる。新しい並びを作る。$`i = 1, \ldots, |C|`$ について $`C_i`$ を足し、$`C_i \ne \bot`$、$`i \lt |C|`$、$`C_{i+1} \ne \bot`$ で、次のどれかが成り立つなら、その後に $`\bot`$ を足す。
  - (L-2-4-1) $`C_{i+1} = C_i`$ で、$`C_i`$ が同じ段の子を持つ。
  - (L-2-4-2) $`C_{i+1} = V_1`$、$`\mathrm{ch}(V_1) \ne ()`$ で、$`C_i`$ が切れていない。
  - (L-2-4-3) ある $`k \le i`$ が、$`C_k = C_{i+1}`$、$`\mathrm{ch}(C_k) \ne ()`$、$`C_i`$ が切れていない、$`i - k + 1 = |\mathrm{sub}(C_k)|`$ を満たす。

  新しい並びを $`C`$ とする。次に**一番上**：
  - (L-2-5) もし $`F`$ の最後の成分が切れているならば、$`L(D) = C`$ である。
  - (L-2-6) そうでなければ、$`C = (C, \bot)`$ とする。ここで $`E`$ を、$`V_2, V_3, \ldots`$ のうち（場所として）$`C`$ の成分でない $`S`$ の並びとする。もし $`E \ne ()`$ で、「$`|E| = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$」でないならば、各 $`E_i`$ について：
    - (L-2-6-1) もし $`i = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$ ならば、飛ばす。
    - (L-2-6-2) そうでなければ、ここで $`H = \mathrm{sub}(E_i)`$、その最後の成分を $`T`$ とし、$`C = (C, H)`$ とする。もし $`T`$ が同じ段の子か、$`z(g) = 0`$ かつ $`y(g) \gt y(T)`$ の子 $`g`$ を持つならば、$`C = (C, \bot)`$ とする。

    そして $`L(D) = C`$ である。

$`\mathrm{kdl}(D, C)`$ は、段の列の同じ段の子の中に入れ子になった、最初の $`D`$ の段の $`\omega`$ の列である。$`C`$ の $`\bot`$ でない各成分 $`c`$ について順に、$`\mathrm{Rest}(c)`$ の中の $`c`$ の同じ段の子 $`g`$ それぞれについて順に、幅優先で探す。待ち行列を $`g`$ で始める。空でない間、先頭から $`h`$ を取り出し、$`h`$ の各子 $`k`$ について順に：
- (kdl-1) もし $`z(k) = 1`$ かつ $`y(k) = y(D)`$ ならば、結果は $`k`$ である。
- (kdl-2) もし $`z(k) = 1`$ かつ $`y(k) = y(c)`$ ならば、$`k`$ を待ち行列の後ろに入れる。
- (kdl-3) もし結果が出ないまま探し終わったならば、$`\mathrm{kdl}(D, C) = \mathrm{none}`$ である。

$`\mathrm{ins}(C)`$ は、段の列の中にある、前の段の列と同じ段の列の段を入れる。空の並び $`O`$ から始める。$`C`$ の各成分 $`c`$ について順に：
- (ins-1) もし $`c \ne \bot`$ で、$`O`$ が $`\bot`$ でない成分を持つならば：ここで $`p`$ をその最後のものとし、$`g`$ を $`h \in \mathrm{Rest}(c)`$ のうち $`z(h) = 1`$ かつ $`y(h) = y(p) \lt y(c)`$ の最初のものとする。
  - (ins-1-1) もし $`g`$ があり $`g \ne p`$ ならば、$`O = (O, L(g))`$ とする。

そして $`c`$ を $`O`$ に足す。結果は $`O`$ である。

**段の数。** $`\mathrm{up}(D) = ()`$ なら $`\mathrm{lev}(D) = 1`$（lev-1）、そうでなければ $`\mathrm{lev}(D) = |L(D)|`$（lev-2）とする。

**鎖を続ける列。** $`\mathrm{chtop}(K)`$ は、$`K`$ が鎖を続け、他の子（または子の無いさらなる 1 段上の子 1 つ）を持つことを表す。ここで $`V = \mathrm{up}(K)`$ とする。
- (chtop-1) もし $`|V| \ge 2`$ で $`\mathrm{sub}(V_1)`$ の最後の成分が切れていないならば：ここで $`E`$ を、$`V_2, V_3, \ldots`$ のうち $`c \ne V_1`$ の $`c`$ とする。
  - (chtop-1-1) もし $`|E| = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$ ならば、真である。そうでなければ、(chtop-2) へ進む。
- (chtop-2) そうでなければ、$`\mathrm{Rest}(K) \ne ()`$ かつ $`V \ne ()`$ のときに真である。

### A.12 記録した項

いくつかの分岐は、項 $`e`$ をキー $`k`$（根の項）の**下に記録する**。$`\mathrm{Img}(k)`$ は $`k`$ の下に記録した項の集合である。$`k`$ が節点なら、それらも節点になる（A.20）。キーは意味を持つ。$`k`$ の下に記録した項は、節点 $`(k)`$ を通してだけ足される。

### A.13 $`\le_2`$ になりうる節点と後者（D7）

$`\mathrm{le2}(t)`$ は、根の項 $`t`$ が **$`\le_2`$ になりうる**か、つまり $`t = \mathrm{root}(P, U + q)`$ と書けるかを決める。
- (le2-1) もし $`y(t) \ne 0`$ か $`\mathrm{ch}(t) = ()`$ ならば、なりえない。
- ここで $`A = \mathrm{ch}(t)`$、$`W`$ をその最後の成分とする。
- (le2-2) もし $`y(W) \ne 1`$ か $`z(W) \ne 0`$ ならば、なりえない。
- ここで $`(\mathrm{hi}, \mathrm{lo}) = \mathrm{split}(W)`$、$`G = \Omega\mathrm{pre}(\mathrm{hi})`$ とする。
- (le2-3) もし $`G = ()`$、$`G \ne \mathrm{hi}`$、$`\mathrm{lo} = ()`$、$`\mathrm{lo}`$ のある成分が $`1`$ でない、のどれかならば、なりえない。
- (le2-4) もし $`\mathrm{c1fixed}(G;\ t, \mathrm{true})`$ が偽ならば、なりえない。
- (le2-5) ここで $`q = |\mathrm{lo}|`$ とする。もし $`G`$ の最後の成分 $`G_n`$ について $`q \gt \mathrm{lev}(G_n)`$ ならば、なりえない。
- (le2-6) そうでなければ、$`t`$ は $`\le_2`$ になりうる。$`A`$、$`W`$、$`U = (1, 0, G)`$、$`q`$ を持つ。

$`\le_2`$ になりうる $`x`$ について次のように書く。$`A = \mathrm{ch}(x)`$。$`P`$ は $`A`$ から最後の成分 $`W`$ を除いたもの。$`G = (G_1, \ldots, G_n) = \mathrm{ch}(U)`$。$`D = G_n`$（**最後の $`\omega`$ の列**）。$`\Lambda = L(D)`$。$`m = 0, \ldots, q`$ について $`d_m = \mathrm{root}(A, U^m)`$、$`\delta_m = \mathrm{ch}(d_m) = (A, U^m)`$（よって $`d_0 = x`$、$`\delta_0 = A`$）。$`K_m = \Lambda_m`$ は $`d_m`$ の段の列である。

**後者。** $`t`$ が $`\le_2`$ になりうるなら $`\mathrm{succ}(t) = (d_1, \ldots, d_q)`$、そうでなければ $`()`$ とする。

**行き止まり。** $`\mathrm{dead}(t)`$ は、$`t`$ がある $`d_m`$ であることを表す。ここで $`A = \mathrm{ch}(t)`$ とする。
- (dead-1) もし $`A = ()`$ ならば、偽である。
- ここで $`U`$ を $`A`$ の最後の成分、$`m`$ を $`A`$ の最後に並ぶ $`U`$ のコピーの数とする。
- (dead-2) もし $`m \ge |A|`$ ならば、偽である。
- (dead-3) そうでなければ、$`\mathrm{root}(A_1, \ldots, A_{|A|-m})`$ がこの $`U`$ で $`\le_2`$ になりえて、$`m \le q`$ のときに真である。

**段の列を持つ後者。** $`\mathrm{d1}(t)`$ は、$`t = d_m`$ でその段の列 $`K`$ が子を持つとき $`(x, K, m, q)`$ を返す。ここで $`A = \mathrm{ch}(t)`$ とする。
- (d1-1) もし $`|A| \lt 2`$ か、$`A`$ の最後の成分が $`y \ne 1`$ か $`z \ne 0`$ ならば、結果は $`\mathrm{none}`$ である。
- ここで $`U`$ を最後の成分、$`m`$ を $`A`$ の最後に並ぶ $`U`$ のコピーの数とする。
- (d1-2) もし $`m \ge |A|`$ ならば、結果は $`\mathrm{none}`$ である。
- (d1-3) ここで $`x = \mathrm{root}(A_1, \ldots, A_{|A|-m})`$ とする。もし $`x`$ が $`\le_2`$ になりえないか、その $`U`$ がこの $`U`$ でないか、$`m \gt q`$ ならば、結果は $`\mathrm{none}`$ である。
- (d1-4) もし $`m \gt |\Lambda|`$ か $`\Lambda_m = \bot`$ ならば、結果は $`\mathrm{none}`$ である。
- (d1-5) ここで $`K = \Lambda_m`$ とする。もし $`\mathrm{ch}(K) = ()`$ ならば、結果は $`\mathrm{none}`$ である。
- (d1-6) そうでなければ、結果は $`(x, K, m, q)`$ である。

### A.14 段の列の子の読み（D8）

$`\mathrm{LK}(x, K, m)`$ は、$`\le_2`$ になりうる $`x`$（その $`U`$、$`q`$、$`D`$、$`\Lambda`$）の段の列 $`K = K_m`$ の子を読む。結果は列の並びである。LK の中の読みは、どれも空の文脈 $`\rho_\varnothing`$ を使う。

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

### A.15 列の子の畳み込み（D8）

$`\mathrm{F}(S;\ x, G, \ell, b, \Delta, t_0, \mathrm{lastG};\ \rho)`$ は、列 $`G`$ の子の読みを和 $`S`$ に畳み込む。$`x`$ は読みが属する根の項、$`\ell`$ は段、$`b`$ は枠の土台（子の並び）、$`\Delta = (\Delta_1, \ldots, \Delta_n)`$ は段の並び、$`t_0`$ は項か $`\mathrm{none}`$ である。添字の像の並び $`I`$ を持ち、初めは空である。ここで $`V`$ を $`z = 1`$ かつ $`y = \ell + 1`$ の $`G`$ の子とし、$`V \ne ()`$ なら $`H = \mathrm{sub}(V_1)`$（そうでなければ $`H = ()`$）とする。$`H \ne ()`$ で $`H`$ の最後の成分が切れていないなら、$`E`$ を、$`V_2, V_3, \ldots`$ のうち（場所として）$`H`$ の成分でなく $`c \ne V_1`$ である $`c`$ とする。そうでなければ $`E = ()`$ とする。$`|E| = 1`$ かつ $`\mathrm{ch}(E_1) = ()`$ のとき真となる旗を $`\beta`$ とする（**子の無いさらなる 1 段上の子 1 つ**）。$`G`$ の各子 $`c`$ について順に、$`\mathrm{lst}`$ を「$`\mathrm{lastG}`$ かつ $`c`$ が最後の子」として：
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

### A.16 畳み込み $`\oplus`$（D9）

$`S \oplus Y`$ は、最初の項が $`S_1`$ の空でない和 $`S`$ と、項 $`Y`$ を取る。
- (fold-1) もし $`Y \le S_1`$ ならば、結果は $`S + (Y)`$ である。
- (fold-2) もし $`Y \gt S_1`$ で $`Y`$ が $`\le_2`$ になりうるならば、結果は $`\mathrm{lh}(Y) + (Y)`$ である。
- (fold-3) そうでなければ、結果は $`\mathrm{lh}(Y)`$ である。

$`S \succ S'`$ は 2 つの和を項ごとに比べる。項が違う最初の位置で、大きい項の方が大きい。一方が他方の頭の部分なら、長い方が大きい。

### A.17 届く先 $`\mathrm{lh}`$（D9）

$`\mathrm{lh}(t)`$ は根の項 $`t`$ の $`\le_1`$ の届く先で、和である。空の文脈から始める。
- (lh-1) もし $`t = 1`$ か $`y(t) \ne 0`$ ならば、$`\mathrm{lh}(t) = (t)`$ である。
- (lh-2) もし $`t`$ が epsilon でないならば、$`\mathrm{lh}(t) = (t) + \lambda(t)`$ である。
- (lh-3) もし $`\mathrm{d1}(t) = (x, K, m, q)`$ ならば（$`t = d_m`$ で $`K = K_m`$ が子を持つ）：
  - (lh-3-1) もし $`\mathrm{Rest}(K) = ()`$ で、「$`m \lt q`$ かつ $`\mathrm{chtop}(K)`$」でないならば（鎖の子だけ）：ここで $`H = \mathrm{sub}(K)`$ とする。$`\Lambda`$ の位置 $`m`$ から $`H`$ を照らし合わせる。$`p = m`$、$`s = 0`$ とし、$`i = m, \ldots, |\Lambda|`$ について：
    - (lh-3-1-1) もし $`\Lambda_i \ne \bot`$、$`s \lt |H|`$、$`\Lambda_i = H_{s+1}`$ ならば、$`s = s + 1`$、$`p = i`$ とする。
      - (lh-3-1-1-1) もしそこで $`s = |H|`$ ならば、繰り返しを止める。

    次に：
    - (lh-3-1-2) もし $`p \lt i \le |\Lambda|`$ のある $`i`$ が $`\Lambda_i = \bot`$ を満たすならば、そのような最初の $`i`$ について $`\mathrm{lh}(t) = (d_i)`$ である。
    - (lh-3-1-3) そうでなければ、$`\mathrm{lh}(t) = (d_q)`$ である。
  - (lh-3-2) もし $`m \lt q`$ かつ $`\mathrm{chtop}(K)`$ ならば：$`\mathrm{lh}(x)`$ を計算する。その計算が $`\mathrm{pre}(x)`$ を記録したならば（LG-3）、$`\mathrm{lh}(t) = \mathrm{pre}(x)`$ である。そうでなければ $`\mathrm{lh}(t) = \mathrm{lh}(x)`$ である。（$`K`$ の子は一番上で、LG-2 で読む。）
  - (lh-3-3) そうでなければ、ここで $`m \lt q`$ なら $`n' = d_{m+1}`$、$`m = q`$ なら $`n' = t`$ とする。$`R = \mathrm{LK}(x, K, m)`$、$`\rho = ((t, y(K), (\mathrm{ch}(n'))),\ (x, y(D)),\ \mathrm{none})`$ とし、$`S = \mathrm{F}((t);\ t, (y(K), z(K), R), y(K), \mathrm{ch}(n'), (\mathrm{ch}(n')), \mathrm{none}, \mathrm{true};\ \rho)`$ とする。
    - (lh-3-3-1) **名前の付いた場合 `kcross`。** もし $`m + 1 = q`$ で、$`K`$ が同じ段の子を持ち、$`\mathrm{blk}(U)`$ ならば、$`y(c) = 0`$ の $`D`$ の子 $`c`$ それぞれについて順に $`S = S \oplus \mathrm{root}(\mathrm{ch}(c))`$ とする。理由：一番上のすぐ下の交差する区間は、一番上での $`x`$ と同じところまで届く。

    そして $`\mathrm{lh}(t) = S`$ である。
- (lh-4) もし $`\mathrm{dead}(t)`$ ならば、$`\mathrm{lh}(t) = (t)`$ である。
- ここで $`A = \mathrm{ch}(t)`$、$`W`$ をその最後の成分とする。
- (lh-5) もし $`z(W) = 1`$ ならば（根の $`\omega`$ の並び）：ここで $`a_1, \ldots, a_k`$ を、$`A`$ の最後に並ぶ $`z = 1`$ の成分の一番長い並びとする。$`S = (t, t)`$ とし、$`i = 1, \ldots, k`$ について $`S = S \oplus \mathrm{root}(A, (1, 0, (\mathrm{Up}(a_1;\ t, 1 = k), \ldots, \mathrm{Up}(a_i;\ t, i = k))))`$ とする。そして $`\mathrm{lh}(t) = S`$ である。
- (lh-6) もし $`t`$ が $`\le_2`$ になりうるならば、$`\mathrm{lh}(t) = \mathrm{lh}_1(t)`$（A.18）である。
- ここで $`(\mathrm{hi}, \mathrm{lo}) = \mathrm{split}(W)`$、$`G = \Omega\mathrm{pre}(\mathrm{hi})`$、$`U = (1, 0, G)`$ とする。
- (lh-7) もし $`G \ne ()`$、$`G = \mathrm{hi}`$、$`\mathrm{c1fixed}(G;\ t, \mathrm{true})`$ ならば（入れ子の極限）：
  - (lh-7-1) もし $`\mathrm{lo} = ()`$ ならば、ここで $`A'`$ を $`A`$ から最後に並ぶ $`U`$ のコピーをすべて除いたものとする。$`\mathrm{lh}(t) = \mathrm{lh}(\mathrm{root}(A', U + 1))`$ である。
  - (lh-7-2) もし $`\mathrm{lo}`$ の成分がすべて $`1`$ ならば、ここで $`r = \mathrm{lev}(G_{|G|})`$、$`S = \mathrm{lh}(\mathrm{root}(A, U + r))`$ とし（ここで $`A`$ は $`W`$ で終わったままであり、$`U + r`$ は $`W`$ の後に足す）、$`S = S \oplus 1`$ を $`|\mathrm{lo}| - r`$ 回くり返す（$`|\mathrm{lo}| \le r`$ なら 0 回）。$`\mathrm{lh}(t) = S`$ である。
  - そうでなければ、(lh-8) へ進む。
- (lh-8) 2 行版の畳み込み。$`S = (t, t)`$ とする。$`i = 1, \ldots, |\mathrm{hi}|`$ について、$`Y = \mathrm{root}(A + \mathrm{C1s}_t(\mathrm{hi}_1, \ldots, \mathrm{hi}_i;\ (), G \ne (), \min(i, |G|)))`$ とし（旗 $`\mathrm{last}`$ は $`G \ne ()`$ のとき真で、位置 $`\min(i, |G|)`$ に渡る）：
  - (lh-8-1) もし $`\mathrm{ch}(Y) = (A, W)`$ ならば（像がまた $`W`$）、$`S = S \oplus \mathrm{root}(P', W + 1)`$ とする。ここで $`P'`$ は $`A`$ から最後の成分を除いたものである。
  - (lh-8-2) そうでなければ、$`S = S \oplus Y`$ とする。

  次に $`\mathrm{lo}`$ の各 $`g`$ について順に：
  - (lh-8-3) もし $`y(g) \ge 1`$ ならば、$`S = S \oplus \mathrm{C1}_t(g;\ (), \mathrm{lg}, \mathrm{false})`$ とする。ここで $`\mathrm{lg}`$ は、$`g`$ が $`\mathrm{lo}`$ の最後の成分のとき真である。
  - (lh-8-4) そうでなければ、$`S = S \oplus g`$ とする。

  そして $`\mathrm{lh}(t) = S`$ である。

### A.18 $`\le_2`$ になりうる節点の届く先（D9）

$`\le_2`$ になりうる $`x`$（A.13 の $`A`$、$`P`$、$`W`$、$`U`$、$`q`$、$`G`$、$`D`$、$`\Lambda`$、$`d_m`$、$`\delta_m`$）に対する $`\mathrm{lh}_1(x)`$。ここで $`r = \mathrm{lev}(D)`$、$`S = (d_q)`$ とする。
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

### A.19 証人（D10）

$`\mathrm{wit}(t)`$ は、$`G`$ の頭の部分の証人の並びである。$`t`$ が $`\le_2`$ になりえないなら空である。そうでなければ（A.13 の $`A`$、$`U`$、$`q`$、$`G`$）、ここで $`(a_1, b_1), \ldots, (a_s, b_s) = \mathrm{grp}(G)`$ とする。各 $`e \in (b_1, \ldots, b_{s-1})`$（最後以外の各組の終わり）について、$`\Pi = (G_1, \ldots, G_e)`$ とする。
- (wit-1) もし $`\mathrm{lim}(G_e)`$ かつ $`\mathrm{cont}(G_e)`$ ならば、証人は無い（その塊が代わりになる）。
- (wit-2) **名前の付いた場合 `lwpos`。** もし $`\mathrm{lim}(G_e)`$ かつ $`1 \lt \mathrm{lev}(G_e) \le q`$ ならば：ここで $`j`$ を、$`G_e`$ の同じ段の子 $`c`$ についての $`\min(\mathrm{lev}(c) - 1,\ q - 1)`$ の一番大きいもの（そのような子が無ければ $`j = 0`$）とする。証人は $`\mathrm{root}(A, U^j, (1, 0, (\Pi, \mathrm{lchain}(y(G_e), \mathrm{lev}(G_e)))))`$ である。理由：共終性。証人は、その中身が読む一番高い後者のすぐ下にある。
- (wit-3) そうでなければ：$`\mathrm{lim}(G_e)`$ なら $`\Pi = (\Pi, (2, 1, ()))`$ とする（そうでなければ $`\Pi`$ はそのまま）。

  どちらの場合も、ここで $`w = \mathrm{root}(A, U^{q-1}, (1, 0, \Pi) + 1)`$ とする。
  - (wit-3-1) もし $`w`$ が $`\le_2`$ になりうるならば、$`w`$ は証人である（$`d_{q-1}`$ と $`d_q`$ の間の最後の区間にある）。

### A.20 パターン（D11）

**閉包。** $`\mathrm{cl}(X)`$ は、$`(), (1) \in V`$ と $`X \subseteq V`$ を満たし、次の操作で閉じた、和の最小の集合 $`V`$ である。
- $`(t_1, \ldots, t_n) \in V`$ から、どの頭の部分 $`(t_1, \ldots, t_j)`$ も、どの $`(t_i)`$ も得る。
- $`(t) \in V`$ から、$`(\mathrm{anchor}(t))`$（$`\mathrm{none}`$ でなければ）、$`\mathrm{lh}(t)`$、各 $`e \in \mathrm{Img}(t)`$ の $`(e)`$、各 $`d \in \mathrm{succ}(t)`$ の $`(d)`$、各 $`w \in \mathrm{wit}(t)`$ の $`(w)`$ を得る。

$`\mathrm{Img}(t)`$ は、1 項の節点 $`(u) \in V`$ の $`\mathrm{lh}(u)`$ の計算（その中のすべての計算を含む）の間に $`t`$ の下に記録した項を持つ。（プログラムは作業の並びでこれらの節点を足す。これは最小の不動点であり、順番によらない。）
- (cl-1) もし $`V`$ の節点が 300 個を超えるならば、プログラムは誤り "too many nodes" で止まる。

**Def 9.4 のコピー**（Carlson 2009, Def 9.4）。$`\le_2`$ になりうる $`x`$ に対して、$`\mathrm{copy}(x)`$ は、$`m = 1, \ldots, 7`$ の $`e = \mathrm{root}(P, U^m)`$ のうち $`\mathrm{dead}(e)`$ が偽の最初のものである。無ければ $`\mathrm{none}`$ である。

**パターン** $`\Phi_3(M)`$。ここで $`\hat{M} = \mathrm{tree}(M)`$、$`V = \mathrm{cl}(\{\hat{M}\})`$ とする。次を多くとも 4 回くり返す。$`J`$ を $`V`$ の 1 項の節点を小さい順に並べたものとし、$`X = \emptyset`$ とする。$`\le_2`$ になりうる各 $`(x) \in J`$ について順に：
- (copy-1) もし $`\mathrm{lh}(x) = (d_q)`$ ならば、飛ばす。
- (copy-2) もし $`u \lt x`$ のある $`(u) \in J`$ が $`\mathrm{lh}(u) = \mathrm{lh}(x)`$ を満たすならば、飛ばす。
- (copy-3) そうでなければ、$`e = \mathrm{copy}(x) \ne \mathrm{none}`$ かつ $`(e) \notin V`$ なら、$`(e)`$ を $`X`$ に足す。

次に：
- (copy-4) もし $`X = \emptyset`$ ならば、くり返しを止める。
- (copy-5) そうでなければ、$`V = \mathrm{cl}(V \cup X)`$ とする。

そして：
- 節点は $`V`$ を $`\mathrm{mat}`$ で並べたもの $`v_0 = () \lt v_1 = (1) \lt \cdots`$ である。
- $`v_i`$ の**届く先**：$`v_i = (t)`$ が 1 項なら、$`\mathrm{mat}(v_r) \le \mathrm{mat}(\mathrm{lh}(t))`$ となる一番大きい $`r \ge i`$ である。そうでないか、そのような $`r`$ が無ければ、$`i`$ である。よって $`v_i \le_1 v_j`$ は、$`i = j`$ か、$`v_i`$ が 1 項で $`i \le j \le \mathrm{reach}(i)`$ のときである。
- **$`\le_2`$ の組**は、$`v_i = (t)`$ と、$`d \in \mathrm{succ}(t)`$ の $`v_j = (d)`$ の対 $`(i, j)`$ である。
- **点**は $`\hat{M}`$ の番号である。
- 加法は、2 行版と同じく A.2 の関係 $`v_i + v_j = v_k`$ である。プログラムは出力しない。

**出力。** 各 $`i`$ について 1 行：$`i`$ が点なら `*`（そうでなければ空白）、$`i`$、$`\mathrm{show}(v_i)`$、`reach` と $`v_i`$ の届く先、$`v_i`$ が $`\le_2`$ の組を持つなら `<=2` とその $`j`$ を小さい順に。

### A.21 コードの中の名前

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
| $`\mathrm{wit}`$, $`\mathrm{cl}`$, $`\mathrm{copy}`$ | `le2_wit`, `closure`, `d94_copy` | $`\Phi_3`$, 出力 | `build`, `show` |
| $`\mathrm{parse}`$, $`\mathrm{tree}`$ | `tss.parse`, `tss.from_mat` | $`\mathrm{cols}`$, $`\mathrm{mat}`$, $`+`$, $`\Sigma`$ | `tss.cols_term`, `tss.mat`, `tss.add`, `tss.addall` |

**コードについての注。** 読みの文脈は大域の積み重ね（`KCTX`、`KDX`、`K1REF`）に置かれ、入れ子の `lh` の呼び出しはそれを空にしない。3290 個の試験の行列すべてで、`lh` を呼ぶたびにそれらを空にしても同じパターンになる。よって本文は空にする形（A.5）で書いた。`C2` と `C2s` の引数 `top` は何もしない。
