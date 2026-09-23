[← Back](README-ja.md) | [English](memo.md) | [Japanese](memo-ja.md)

# メモ：議論と作業の現在地

これからやることは [plan-ja.md](plan-ja.md) にある。このファイルには理由と経緯を残す。

議論の全体がどういう形をしていて、作業が今どこまで進んだかを書く。次の一手を
選ぶ前に、まずここを読む。対になるのが [spec-ja.md](spec-ja.md) で、
ライブラリが何であるかと、書き方の規約をまとめてある。

## 何のためのライブラリか

巨大数の系——BMS、DBMS、Y 数列——は、行列や数列の上の書き換え系であり、問いは
「どの展開列も有限で止まるか」である。ライブラリはこれに標準的な方法で答える。
整列集合への測度で、一歩ごとに狭義に下がるものを見つける。

だから半分が 2 つと、その間の橋になる。

```
Notation/<系>/    系そのものと、順序数表記系
Trans/            それらの間の翻訳
Core/             共通の定理。測度 ⟹ 停止性
```

要点は、どの半分も**一度だけ**証明されることである。新しい系は 3 つのフィールドと
測度 1 つを出せばよく、残りは定理として受け取る。

## 1 つの系についての連鎖

後ろから読むと、作る順序になる。

```
BMS は停止する
  ⇐ Sim BMS ExBuchholz                    翻訳
  ⇐ WellFounded OTLt                      行き先が整礎
  ⇐ 標準形の主項が全部可到達
  ⇐ val が OT 上で狭義単調               表記系が正しい
  ⇐ ψ についての順序数の事実
```

最後の 2 つ以外は全部 `Core` が出す。最後の 2 つが、その表記系固有の数学である。

## 今どこまで来たか

### `Core/` — 完成

| ファイル | 中身 |
|---|---|
| `WF.lean` | `not_descending`、`not_wellFounded_of_descending` |
| `Rewrite.lean` | `Rewrite`、`Terminates`、`WF`、`terminates_of_wf`、`wf_of_measure`、`terminates_of_measure` |
| `Std.lean` | `Rewrite.Std`。標準形と生成元 |
| `Morphism.lean` | `OrdHom`、`Sim`、`StepHom`、`Equiv`、`Eval` と移送定理 |

`Googology/Rank.lean` がその隣にある。整礎な系は自前の順序数の測度——一歩の関係の
階数——を持つ、という定理である。`StepHom.rank_map` はその測度が、ステップの上へ
写す埋め込みで変わらないと言う。`Trans.BMS.rank_prim_eq_val` は、1 行ではそれが
項の値だと言う。mathlib が要るので `Core` には入れていない。

`sorry` なし、外部依存なし。停止性だけが欲しいプロジェクトは、これだけ import
すればよい。

### `Notation/ExBuchholz/` — 試験台。済

| ファイル | 状態 |
|---|---|
| `Basic.lean` | 済。項、`cmp`、決定可能性 |
| `Order.lean` | 済。狭義線形順序と非狭義の順序 |
| `Std.lean` | 済。`G`、`isOT`、`OT`、決定可能 |
| `WF.lean` | 済。`not_wellFounded_lt`、`cmp_cons_cons'`、`OT` の構造補題、`OTLt` |
| `Sum.lean` | 済。主項の可到達性を仮定した `wellFounded_OTLt` |
| `Ord.lean` | 済。順序数の上の `ψ`、濃度評価、下方閉包性、加法的主要性 |
| `Opow.lean` | 済。`p0` の閉じた形。`e0` 未満で `w^a`、`e1` 未満で `e0·w^a`。正規形定理の最初の二歩 |
| `Level.lean` | 済。同じことを全添字で。`p_v(a) <= W_v·w^a`。最小不動点未満で等号。`p_v(W_{v+1})` がその不動点 |
| `Eps.lean` | 済。有限の全段での `p0(W·(n+1)) = e_n`。帰納法一本。`p1(1) = W·w` と `p0(W·w) = e_w` |
| `Ladder.lean` | 済。同じことを `z0` 未満の全ての `g` で。e 関数と `W` による除算 |
| `LadderV.lean` | 済。同じことを全添字で。`z^v` 未満で `p_v(W_{v+1}·(1+g)) = e^v_g` |
| `Eval.lean` | 済。`val`、`Lam`、`val_mem_CSet`、`ψ` の比較補題 2 本 |
| `Mono.lean` | 済。同時帰納、`val_lt_val`、`OTLt_wf` |
| `FS.lean` | 済。`dom`、`fs`、`fs_lt`、`dom_eq_one_or_tw`、`step_lt`、`exb` |
| `Closure.lean` | 済。Buchholz 3.4、3.5、3.6、Bachmann 性、そこから 3.3。`bachmann`、`OTFS_thm`、`Trian_fs_thm` |
| `System.lean` | 済。可算標準形の上の `exbOT`、`exbOT_wf`、`exbOT_terminates` |
| `NF.lean` | 済。正規形定理の順序数側。`M`、`M_mem_of_comp`、`M_psi_mem`、`arg_mem_of_psi_mem` |
| `Onto.lean` | 済。`val` が `C_0(Λ)` の上へ全射であること。`Vals_eq`、`valEquiv`、`existsUnique_OT_of_lt_psi_Lam` |

**`ExBuchholz` は完成した。**`OTLt_wf` が標準形の上の順序は仮定なしで整礎だと
言い、`exbOT_terminates` が可算標準形の上の展開系は止まると、これも仮定なしで
言う。`Vals_eq` が `val` は `C_0(Λ)` の上へ全射だと言うので、`val_inj_of_OT` と
合わせて出典の述べる順序同型になり、`p0(Λ)` 未満の順序数はどれもただ一つの
標準形を持つ。

### `Notation/BMS/` — 済

行数が任意のバシク行列。`bms_terminates r` がどの `r` でも成り立つ。
`r = 1, 2, 3` が原始数列・ペア数列・トリオ数列である。
`Notation/BMS/Any.lean` はさらに進む。**どんな**配列からでも展開は止まるので、
標準性の条件を付けない規則 `bmsAll r` も停止し、`bms r` も
`Notation.DBMS.dbms r` もその中に入る。

停止性の証明そのものは
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern)——
`R_r` のラベルと Σ 初等部分構造による——で、このパッケージはそれを依存に持つ。
`Notation/BMS/Basic.lean` が出すのは `Rewrite` の 3 フィールドと
`Subrelation.wf` 1 本だけで、残りは `Core` が出す。向こうの `Pat.StdR` が
こちらの `Rewrite.Rel` を手で書き下したものになっていたので、合わせ込みは
要らなかった。

### `Trans/` — 1 行は完了。階層と、2 行の最初の順序数も

`Trans/BMS/` は 1 行の BMS を拡張ブーフホルツ項に翻訳し、また戻す。読み取りが
`read` と `unread`、1 行での `BM4.expand` が `OneRow.lean`、`[ ]` との可換性が
`Commute.lean`、添字の突き合わせが `Cut.lean` と `Entries.lean`、`StepHom` と
そこから出る順序数が `Prim.lean` と `Bms.lean` である。

系どうしの関係も扱う。`EntriesR.lean` が行数によらず規則を成分列の上に書き、
`Agree.lean` が 1 行・2 行・一般の規則は一つの規則だと言い、`Same.lean` が一般の
系の 1 行と 2 行は原始数列系とペア数列系**そのもの**だと言い、`ZeroRow.lean` が
下に 0 の行を足しても規則も順序数も変わらないと言う。だから `r ≤ s` なら `bmsL r`
は `bmsL s` の中に入る。

`Eps0.lean` が 1 行を順序数として閉じる。名指すのは `e0` 未満ちょうどである。
`val` の全射性は `e1` まで伸ばしてある。`EpsN.lean` がそれを全ての `e_n` まで運び、
`Arg.lean` と `EpsBig.lean` が `e_{e0}` まで、`Zeta.lean` が `z0` まで運ぶ。
`RankVal.lean` は系の階数がその順序数だと言い、2 行の最初の階数を計算する。
`Append.lean` は展開がブロックを越えて戻らないと言い、そこから階数はブロックに
ついて加法的になる。

### `Notation/DBMS/` — 済

同じ規則で、生成元の列 `i` の行 `k` が `i - k` になったもの。`dbms_terminates`・
`dbms_wf`・`dbmsEval` がどの行数でも成り立つ。`bmsAll` への包含から出る。

### `Notation/Y/` — 済

公式の展開をプログラムから書き起こしたもの。`ySys` と種がある。項目 4 にある。
停止性はここの定理である。`WellOrder/` に移植した証明から `WellFounded.lean` が導く。

## ExBuchholz の整礎性 — 済

```
val は OT 上で狭義単調:  x < y → OT x → OT y → val x < val y
```

が `OrdHom.wf` を通して `wellFounded_OTLt` の仮定を外した。無条件の形が
`OTLt_wf` である。

`ψ_v` の弱い単調性では足りない。`ψ_v(a) = ψ_v(a+1)` は実際に起きる。`a` が
`C_v(a)` の中に届かないときである。狭義にするのが標準形の条件の役目である。
4 段階ある。

| # | 段階 | 状態 |
|---|---|---|
| 1 | 閉包の元で十分小さいものは `ψ_v(a)` より下 | 済（`mem_CSet_of_le`、`lt_psi_of_mem`） |
| 2 | したがって `ψ_v(a)` は加法的主要 | 済（`isPrincipal_add_psi`） |
| 3a | **添字**は必ず自分の閉包の中にある | 済（`val_mem_CSet`、`val_lt_Lam` 経由） |
| 3b | **引数**も同様。ここで `G` を読む | 済（`val_mem_CSet_arg`） |
| 4 | 項の比較を値の比較に組み立てる | 済（`val_lt_val`） |

### 3b と 4 が一緒になった理由

3b には 4 が必要である。`G a (cons c d r)` は `a ≤ c` で場合分けしるが、もう一方の
枝では構文的に `c < a` が成り立っていて、証明に `val c < val a` が要る。これが
4 そのものである。逆に 4 にも 3b が必要で、2 つの主項が添字を共有する場合がそれに
あたる。

だからこれは 1 つの同時帰納になる。測度は、単調性の側が `size x`、閉包の側が
`size a + size t` である。単調性の側で左の項だけを見るのは、`b` から `G` が集めた `z`
についての呼び出し `(z, b)` が、右の項では抑えられないからである。どの呼び出しも
狭義に下がる。

* 4（`(cons a b t, cons c d u)`）は 4 を `(a,c)`、`(b,d)`、`(t,u)`、`(t, ψ_c(d))`
  で呼び、3b を `(a,b)` で呼ぶ
* 3b（`(a, cons c d r)`）は 3b を `(a,c)`、`(a,d)`、`(a,r)` で呼び、4 を `(c,a)`
  で呼ぶ

それが `Mono.lean` である。

## 次

1. **済：拡張 Buchholz 項は停止する。** `System.lean` に可算標準形の上の展開系
   `exbOT` があり、`exbOT_wf` と `exbOT_terminates` を無条件に証明してある。
   道筋は 3.2(b)、3.4、3.5、`SubBound`、3.6、3.3、Bachmann 性で、どれも仮定
   無しの定理になった。`test/ExBuchholzCheck.lean` の計算とも合う。サイズ 8
   以下の可算標準形 3835 個を `0`〜`4` のどれで展開しても標準形・可算・狭義減少
   が保たれる。サイズ 9（15890 個）でも同じ。ε₀、ψ_0(Ω+Ω)、ψ_0(ψ_1(1))、
   ψ_0(Ω_2)、ψ_0(ψ_Ω(0)) は途中の項が全部標準形のまま `0` に到達する
2. **1 行については完了: BMS がどの順序数を名指すか。** `Trans/BMS/` に一本の
   鎖がある。`read` は行をそのときの水準より上でない成分で区切り、ブロックを
   その上のブロックが読む項の `ψ_0` に送る。`read_expandL` は読み取りが展開を
   `[ ]` に変えると言う。二つの流儀の差である付け替え `N ↦ N + 1` を込めてである。
   `entries_expand` は `BM4.Arr 1` 上の `BM4.expand` を成分列の規則と突き合わせる。
   出てくる値が `bmsOrdEval` で、`bms_one_terminates` も一緒に出る。1 行の停止性が
   ラベルの証明ではなく拡張ブーフホルツ ψ の整列性から出るということである。
   両方向とも決着している。`lt_e0_iff_allNil` は標準形が `p0(W)` 未満で
   あるのは添字が全部 0 のときちょうどであると言い、`exists_read` はそのすべてが
   どれかの行列から読み取られると言う。つまり 1 行は `p0(W)` 未満を取りこぼさず、
   それ以上を名指さない。項としてだけでなく順序数としてもそうである。
   `Ord.psi_Omega_one` が `p0(W)` は `e0` **そのもの**だと言い、
   `exists_OT_of_lt_eps0` が `val` はその未満の順序数の上へ全射だと言う。証明は
   Cantor 標準形で、そこでの `p0(a) = w^a` は `Ord.psi_zero_eq_opow` である。
   だから `exists_matrix_of_lt_eps0` と `val_read_lt_eps0` が、1 行の行列が名指すのは
   `e0` 未満の順序数ちょうどだと言う。`rank_prim_eq_val` が輪を閉じる。表記系なしで
   定義できる展開関係の階数が、その値**そのもの**である。だから `Rewrite.rankEval` を
   「行列が名指す順序数」と読んでよい。両方が定義されているところで一致している。
   DBMS の 1 行は同じ系なので、同じ二つの主張が成り立つ。さらに 2 行の順序数が
   一つ出る。`rank_pairGen` は生成元 `(0,0)(1,1)` の階数が `e0` だと言う。これは 0 の行
   が付いた 1 行の行列へ展開し、`BMS/Embed.lean` がその順序数をそのまま運ぶからである。
   つまりペア数列系は原始数列系が終わる所から始まる。2 行の読み取りは無いままで
   そう言える。`rank_gen_eq_iSup` はこれをどの行数でも言う。`r + 2` 行の生成元の階数は
   `r + 1` 行の生成元たちの階数の極限である。言えないのは `(0,0)(1,1)(2,2)` 以降の
   生成元の階数で、そちらの展開は 0 の行を持つ行列にならない。`BMS/Append.lean` が
   加法の構造を足す。展開は行 `0` の成分が `0` の列を越えて戻らないので、階数はその
   ブロックについて加法的である（`rank_appendState`）。ブロックの `n` 個並びは階数が
   `n` 倍になる。もう半分が `expandRL_of_m0_zero` である。`m₀ = 0` なら展開は固定
   部分とブロックの `N + 1` 回の繰り返しなので、`rank_mul_omega0` がそのブロックの
   階数を `w` 倍する。そこから 2 行の値が三つ出る。`(0,0)(1,0)` は `w`——0 の行が
   そう要求する——、`(0,0)(1,1)(1,0)` は `e0·w`、`(0,0)(1,1)(0,0)(1,0)` は `e0 + w`
   である。`rank_split_mul_omega0` が二つをまとめるので、この形の行列は 3 行で済む。
   仮定は両方 `rfl` である。これらが出す階数は、`1` と `e0` を `+` と `·w` で閉じた
   集合の中に入る。三つの規則を合わせるとそうなる、という意味であって、その閉包が
   全部実現されると主張しているのではない。上の行列は証明した実例である。実例の
   一つは単発ではなく族である。`rank_MkState` が、どの `k` でも
   `(0,0)(1,1)(1,0)^k` の階数は `e0·w^k` だと言う。だから 2 行の系の順序数は
   少なくとも `e0·w^w` になる。出典が置く値よりはるかに低いが、読み取り無しで
   階数が届くのはそこまでである。届かない
   のは `(0,0)(1,1)(2,2)` 以降の生成元で、そちらの展開は 0 の行の行列でもブロックの
   繰り返しでもない。

   `prim` の状態、つまり項が標準形である行列は、標準 1 行行列とちょうど一致する
   （`std_entries_iff`）。さらに `primEquivE0` は `Equiv` である。原始数列系と
   `p0(W)` 未満の標準形は、互いに模倣し合う二つの系ではなく、一つの系の二通りの
   書き方である。そこでの `[ ]` が何かは `fs_lub` が言う。項は
   `X[0] < X[1] < ⋯` の上限である。鍵は `exists_le_fs`、`p0(W)` 未満で `[ ]` が収束すると
   いうことで、これにより生成元からの降下が任意の行列にちょうど着地する。定理では
   なく照合のまま残っているのは、`Pat.Std` と参照実装がどの行列を標準とするかで
   一致すること。長さ 5、成分 4 未満の 1024 通りで一致する（`test/TransCheck.lean`）。

   2 行は Bachmann–Howard 順序数ではなく `p0(W_w)` に届く。
   [yaBMS](https://github.com/koteitan/yaBMS) の対応表に
   `(0,0)(1,1)(2,2) = p0(W_2)` とあり、これが Bachmann–Howard 順序数そのものである。
   さらに `(0,0)(1,1)(2,2)(3,3) = p0(W_3)` なので、生成元は有限の添字を全部登り、
   上限は `p0(W_w)` になる。これは規則性とも合う。`r` 行の生成元は `r-1` 行の系が
   終わるところから始まる。`(0)(1)…(n)` は `w↑↑n` で上限 `e0 = p0(W)`、それが
   `(0,0)(1,1)` である。そして `(0,0,0)(1,1,1) = p0(W_w)` である。だから 2 行の
   読み取りは `p0` と `p1` だけでなく、有限の添字すべてで `p` を使う必要がある。
   3 行以上は未解決なので、次の目標は `r = 2` である。最初の部分はできている。`BMS/Rows.lean` が行数によらず
   bad root を確定させ、`BMS/TwoRow.lean` が 2 行の列写像を読み出す。`m₀` は 0 か
   1 で、1 のとき、bad part での位置が bad root の行 0 祖先である列について行 0 に
   加算が入る。`BMS/Anc.lean` がその祖先関係を成分列の上で与え、計算できる形にする。
   そして `BMS/Entries2.lean` が二つを合わせる。`expand2L` が規則全体を成分列の上に
   書いたもので、`entries2_expand` がそれは `BM4.expand` だと言う。実際に動き、
   長さ 4 以下、成分 3 未満の 2 行行列すべて（標準形 46 個、展開 138 通り）で参照実装と
   一致する（`test/TransCheck.lean`）。`BMS/Pair.lean` がそれを生成元付きの `Rewrite`
   として包み、停止性を運ぶ。`BMS/EntriesR.lean` は**任意の行数**で同じことをする。
   どの行でも `parent A k` と `anc A k` を与え、`expandRL` と `entriesR_expand` を
   出す。だから BMS の展開はどれも走る。配列の形は走らない。3 行では、長さ 3 以下・
   成分 3 未満の標準行列 24 個の展開 72 通りすべてで参照実装と一致する。
   `BMS/Agree.lean` が三つの規則を結ぶ。1 行と 2 行での `expandRL` は `expandL` と
   `expand2L` である。そして一般の規則を `bmsL r` として包み、`bmsL_terminates` と
   `bmsLStd` を付ける。`BMS/Same.lean` が系どうしを結ぶ。`bmsL 0` は `prim`、
   `bmsL 1` は `pairL` で、いずれも `Equiv` である。

   つまり 2 行の機械的な部分は終わっている。残っているのは読み取りで、これは機械的な
   仕事ではない。2 行の読み取りは有限の添字すべてで `p` を使う必要があり、それを書き
   下すということはペア数列の順序数解析を再構成するということである。対応表ではそれは
   できない。表は写像を 20 点で固定するだけで、規則の方は推測に任される。20 点に合う
   推測した規則というのは、Y 数列を、そのプログラムを書き起こすまで入れずにいた理由の
   失敗そのものである。調べた資料に規則は書かれていない。
   [wiki の記事](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0)
   は対応を例ごとにハーディ階層で近似して導き、名前の付いた順序数ごとに区切っている
   だけで、写像そのものは一度も書き下されていない。取りかかれるようにするのに要るのは、
   値の表でも一つずつの導出でもなく、写像の定義文である。その後の可換性では、1 行では決して現れない `[ ]` の節、タワーが出てくる。
   その `dom` の三分法には 1 行では決して現れない第 4 の場合、タワーが出てくる
4. **DBMS は済、Y 数列は定義済。** `Notation/DBMS/` に展開系がある。規則は BM4 の
   ものそのままで、違うのは生成元だけである。列 `i` の行 `k` が `i` ではなく
   `i - k` になる。停止性はどの行数でも成り立つ。しかもそれは生成元のおかげ
   ではない。`Notation.BMS.terminates_any` が、標準形かどうかに関係なくどんな配列
   からでも展開は止まると言う。高さが降下するラベルは `Λ` 鎖で、配列を一度も見ない
   からである。取り込んでいる `Pat.terminates` の `Std` 仮定は、配列が何を名指すか
   についてのものであって、止まるかどうかについてのものではない。1 行は
   BMS と同じ翻訳で済んでいる。
   `Notation/Y/` に Y 数列（1-Y）がある。公式の定義はプログラム、
   [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の `script.js`
   である。`Yukito.lean` はそれを文ごとに写した koteitan の書き起こしで、
   [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) から
   持ってきた。`ySys` は `(1, h+1)` から到達できる列の上の系である。
   `test/YCheck.lean` が `expand` をプログラム自身の出力と 213 件で比べ、
   `(1,2,4,8,10,8)` を含めて全部一致する。停止性は今はここの定理である
   （下の 2026-09-23）。最初は引用だった。Phyrion 氏の
   [1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)
   が独立に定義した展開について証明し、1y-expand-equiv の `expand_eq` がその展開と
   ここの展開が等しいことを証明する。どちらも Lean 4.33.1 である。Phyrion 氏の
   一式を import するには、このライブラリと依存を Lean 4.33.1 に移し、ライセンスの
   無い BMS のスナップショットも取り込む必要があった。
   [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) がそのスナップショットを
   取り除いたので、代わりにそれと 1y-expand-equiv のファイルを Lean 4.30.0 へ移植した。

## 今どこが前線か

機械的な部分は全部終わっている。展開は行数によらず走る関数であり、それが
`BM4.expand` である。各系は生成元付きの `Rewrite` になっている。1 行・2 行・一般の
形は互いに同じものだと証明されている。1 行は順序数まで両方向で決着し、同値にも
なっている。

階層も決着した。`BMS/ZeroRow.lean` が、下に 0 の行を足しても規則は何も変わらない
ことを行数によらず言う。`r + 2` 行の生成元 `(0,…,0)(1,…,1)` を `N` で展開すると
`r + 1` 行の生成元に 0 の行が付いたものになるので、`bmsL r` は `bmsL (r + 1)` の
中に入る。繰り返せば `s ≥ r` なるどの `s` についても `bmsL s` の中に入り、全行列の
側でも同じことが成り立つ。`rank_zeroRow` は順序数も両側で同じだと言うので、足した
行は何も新しく名指さない。

1 行は順序数としても決着した。`val` は `e0` 未満の順序数の上へ全射である。
`Trans.BMS.exists_OT_of_lt_eps0` が Cantor 標準形でそれを言い、そこでの
`p0(a) = w^a` は `Ord.psi_zero_eq_opow`、`p0(W) = e0` は `Ord.psi_Omega_one`
である。だから `exists_matrix_of_lt_eps0` と `val_read_lt_eps0` が、1 行の行列が
名指すのは `e0` 未満の順序数ちょうどだと言う。

表記系そのものも決着した。**`val` は標準形から `C_0(Λ)` への順序同型である。**
出典が述べているのはこれである。全射の半分が `Notation.ExBuchholz.Term.Vals_eq`
で、`valEquiv` が単射の半分とまとめる。だから `p0(Λ)` 未満の順序数はどれも、ただ
一つの標準形の値である（`existsUnique_OT_of_lt_psi_Lam`）。可算な標準形が名指す
のはちょうどそれらである（`val_lt_psi_Lam_iff`）。項の順序で可算な `X` の下に
ある標準形は `val X` 未満の順序数そのものである（`belowEquiv`）。`X` の下の順序型が
`X` の名指す順序数になる。これは他の系の読み取りが `[ ]` との可換性なしに使える形で
ある。その系の標準な状態を順序ごとこの項に対応させれば、状態の下の順序型が項の値に
なる。

止まっていたのは collapse の節である。`p_u(e)` の標準形の引数は自分の閉包に入って
いなければならず、その引数は一般に `e` より大きい。`p0(e0) = p0(W)` で、標準形が
使うのは `W` である。`Notation/ExBuchholz/NF.lean` は引数を `M(e)`、すなわち
`C_u(e)` の `e` 以上で最小の元へ持ち上げる。これは閉包も値も変えない
（`Ord.psi_M_eq`）。そのうえで、`+` と `W_·` と `e` 未満での collapse で閉じた
集合から `M` が出ないことを示す。順序数の `M` は Cantor 標準形の各項の `M` から
読める（`Ord.M_mem_of_comp`）。項 `p_t(h)` の `M` は `p_t(M(h))`、`W_{t+1}`、
`W_{M(t)}` のどれかである（`Ord.M_psi_mem`）。その集合に値の集合を置けば、`e` に
ついての帰納法で項が得られる。`C_v(b)` を置けば、同じ論法で閉包を `G` で読む
Buchholz の補題（`Term.G_lt_of_mem_CSet`）が得られる。これが「`M(e)` は自分の
閉包に入る」を標準形の条件に変える。

`Trans/BMS/` の、`e1`、`e_w`、`e_{e0}`、`z0` へ届く構成が先にあり、いまも残して
ある。項を手で作り、どの項がどの順序数を名指すかを言う。一般の定理はそれを
言わない。

残る問題は一つで、Lean の問題ではない。

* **2 行以上の読み取り。** 行列から順序数への写像の定義文が要る。3 行についてはそれが
  ある。[koteitan/trio](https://github.com/koteitan/trio) が `p0(W_a)` から trio 数列系
  （3 行行列の `z < 2` 部分）の標準形への写像を
  [アルゴリズム頁](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md)
  に書き下ろしており、値は
  [対応表](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/1/README-en.md)
  にある。`Trans/BMS/Trio.lean` がその `a < e0` の側を `omegaIndexMatrix` として転記し、
  対応表の 20 行で検算してある。`p0(W_1) = e0` が `(0,0)(1,1)`、`p0(W_2)` が
  `(0,0)(1,1)(2,2)` で、後者は yaBMS の表が Bachmann–Howard 順序数を置く場所でもある。
  これは転記と `#guard` であって定理ではない。ただし出力の形だけは定理にしてある。
  `WF3_omegaIndexMatrix` と `WF3_trioMatrix` が、どの列も 3 行で `z < 2` だと言う。
  証明していないのは、写像の像が標準形であること、単調であること、`[ ]` を基本列に
  直すことの三つで、1 行では揃っているものである。前の二つはその 20 個の行列について Lean の外で参照実装と照合した。20 個とも
  標準形で、`α` が増えると行列も `<` で増える。三つ目は**そのままでは成り立たない**。
  3 行の `BM4.expand` と表記系の正準基本列は別の割り当てである。見つかった最小の例が
  `p0(W_{w^w})` で、行列の展開は `p0(W_{w^3})` の行列になるのに対し、項の `X[1]` は
  `p0(W_w)` である。だから交換法則を定理にするなら、等号ではなく共終性で比べることに
  なる。アルゴリズムの `e0 <= a < Λ` の側（指数の埋め込みが原始数列ではなく表記系全体に
  なる所）はまだ転記していない。

  読み取りが無い間は、階数なら個別の値には届く（`rank_pairGen`、
  `rank_gen_eq_iSup`、`rank_succAll`、`rank_omegaAll`）。ただし展開がすでに分かって
  いる所に限る。生成元、親を持たない列、それに `BMS/Append.lean` が届くブロックの
  繰り返しである。`(0,0)(1,1)(2,1)` はそのどれでもない。そこは `m₀ = 1` なので各
  コピーに加算が付く。`(0,0)(1,1)(2,0)` は繰り返しだが、繰り返すのが `(1,1)` で、
  ブロックで始まらない部分は自分の階数を持たない。階数が届く所では、その順序数に
  名前も付く。どの値も拡張ブーフホルツ項の値である（`rank_genAll_val` とその隣の
  五つ）。だからそれらの行列については、表記系の言葉でも答えが出ている。

## 約束ごと

* 主張は全部 Lean の定理で、`sorry` も追加公理もありない
* `#guard` の行は小さい場合の計算であって、定理ではない。見た目で分かるように
  分けてありる
* `Core` は mathlib を import しない。表記系が import するのは、順序数へ評価する
  ときだけである

## 2026-09-23：2 行と、拡張ブーフホルツ項の階数

- ペア数列は、Lake の依存 koteitan/pss-proof の `Trans` を通して順序数に翻訳した。
  `Trans/PSS/` が、その展開が `expand2L` であること、その Buchholz 項が `p0(W_w)`
  未満の標準的な拡張ブーフホルツ項の上へ写ること、ペア数列の階数がその項の
  `1 + val` であることを証明する。ペア数列系は `p0(W_w)` に届く。
- `Notation/ExBuchholz/Cofinal.lean` が、塔の場合も含めて、どの可算標準形でも基本列が
  共終であることを証明し、`RankVal.lean` が `exbOT` の階数は `val` だと証明する。
- 1 行の DBMS の翻訳写像は、文字どおりには単射でない。`dbms 1` の状態は行列の外にも
  値を持つからである。`Trans/DBMS/Tables.lean` が反例と、成分の上での単射性を証明する。
- Phyrion 氏の Lean と同じ展開（weak magma、no extraction）の ω-Y を、patterns of
  resemblance で再証明した（[koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por)、
  2026-09-23）。これは公式の ω-Y とは別の数列システム（weak-magma ω-Y）として扱う。
  公式の ω-Y は koteitan/wy-wo-por で扱う。

## 2026-09-23：Y 数列の停止性をここで証明

- `Notation/Y/WellOrder/` は、koteitan/1y-wo-por（`ZeroY/`、`OneY/`、`Por/`。
  Apache-2.0）と koteitan/1y-expand-equiv（`Equiv/`。書き起こしの写しは除く）を
  Lean 4.33.1 から Lean 4.30.0 へ移植したものである。203 モジュール、約 40,000 行。
  変えたのは import と 7 個の証明だけである。Lean 4.30.0 では、命題の中に書いた
  `match` の選択肢に `save_info` の注釈が残る。`match` を簡約した後、その下の
  引き算が `omega` から見えない。`WellOrder/Port.lean` のタクティク `strip_mdata` が
  注釈を取り除く。`Equiv/Row0.lean` はもう一か所変えた。`Por.BMS.greatestBelow?` は、
  ライセンスの無い `YesMetaZFC` の版と違って、再帰で定義されていないからである。
- `Notation/Y/WellFounded.lean` が `Por.expansion_wellFounded` と
  `Yukito.expand_eq` をつなぐ。`expand_eq_numeric` は、`Basic.lean` の燃料で、
  空の列も含めて合法な列すべての上で `expand` が `OneY.Numeric.expand` に等しい
  ことを言う。そこから、標準形の上の `ySys_wf`、`ySys_terminates`、
  `yStd_terminates`、`yEval`、合法な列すべての上の `yLegal_wf`、
  `yLegal_terminates`、標準形の辞書式整列 `yStd_strictWellOrder` が出る。
- README の非標準の列は `yLegal` を数える。その状態は、項が正で先頭が `1` の列
  すべてである。それ以外の列については何も証明していない。

## 2026-09-23：目標の一覧と README の検査

- 目標の記録の仕方は [spec-ja.md](spec-ja.md) の 7 節にある。記録は
  `Googology/Core/Goals.lean`、`Googology/Goals/Basic.lean`、
  `Googology/Goals.lean` にある。記録は 18 個、監査の行は 77 行である。
- README は生成しない。`scripts/check_readme.py` は監査と、`README.md` と
  `README-ja.md` の表を読む。一致しないと `1` で終わる。
- `test/GoalsAudit.lean` が `Test` ライブラリに入っているので、`lake build`
  （既定のターゲット）が記録を作り、監査を出力する。検査は次のとおり。

  ```sh
  lake env lean test/GoalsAudit.lean > audit.txt
  python3 scripts/check_readme.py --audit audit.txt
  ```

  `lake build` や `leanman check` の出力を `--audit -` にパイプで渡してもよい。
  2026-09-23 の時点で検査は `0` で終わる。公理は `propext`、
  `Classical.choice`、`Quot.sound` である。
- 記録が README の文より少ないことしか言っていない所：
  - 「2 行以下の BMS」は項の並び（`prim`、`pairL`）の上で記録している。
    `bms 1` と `bms 2` の配列の上ではない。配列の上では、1 行の DBMS と同じ
    理由で「単射性」が成り立たない。
  - 拡張ブーフホルツ ψ の「全射性」：像は $`\psi_0(\Lambda)`$ 未満の順序数
    である。$`C_0(\Lambda)`$ 全体ではない。`exbOTStd` は `Standard := True`
    であり、生成元から届く集合ではない。
  - `bmsNotation`、`dbmsNotation`、`bmsToSucc` は、すべての `r` について
    `r + 1` 行を扱う。
  - 写像の無い行（たとえば「3 行以上の BMS」）には記録が無い。spec-ja.md の
    7.5 により、そのセルは空である。
- ❌ のセルのうち 5 個は、今ある定理から数行で証明できる。一時ファイルで確かめた。
  README と一致したままにするため、記録にはつないでいない。
  [plan-ja.md](plan-ja.md) に載せた。
- 目標の一覧の検査で見つかった 5 つのマスを ✅ にした（2026-09-23）：ペア数列 → 拡張ブーフホルツ ψ の階数を保つ（`pairToExb_rank`）、BMS `r` 行 → `r+1` 行の単射性（`bmsToSucc_injective`）、DBMS `r` 行 → BMS `r` 行の展開と可換・単射性・階数を保つ（`dbmsToBms_commutes`、`dbmsToBms_injective`、`dbmsToBms_rank`）。どれも `Googology/Goals.lean` の Bridges の節にある。

## 2026-09-23：行列の上の 1 行の DBMS

- DBMS の標準形は行列そのものである。`dbms 1` の状態は配列で、配列は行列の外の値も
  持つ。そのため二つの標準な配列が、一つの標準形になることがある。作者は、単射性を
  行列の上で述べることに決めた。
- `Trans/DBMS/OneRowL.lean` で、成分の上の 1 行の DBMS `dbmsL1` を定義した。状態は
  標準な配列の成分の列、展開は `expandL`、空の列で停止する。`dbmsL1Std` は生成元
  `(0)(1)⋯(n)` を与える。`dbmsToL1` は配列からこの系への `StepHom` で、階数と順序数を
  保つ。`dbmsL1EquivPrim` は、この系が原始数列の系そのものであることを言う。
- 記録 `dbmsOneRowOrd` と `dbmsToPrim` は `dbmsL1` を使うようにした。順序数への翻訳
  写像の表の行「1 行の DBMS」は 6 列とも ✅ になり、1 行の DBMS → 原始数列のマスは
  ✅✅✅✅✅✅ になった。
- 配列の上の反例（`dbmsOrdEval_not_injective`、`dbmsHom_not_injective`）は残した。
  これは表し方 `Arr 1` についての正しい命題で、標準形についての命題ではない。
- トリオとペアの 5 項目（2026-09-23、branch `feature/trio-pair`）。
  - `Trio.lean` の写像は、`a < e0` で 3 行の BMS の標準形に入る（`trioMatrix_std`、`Trans/BMS/TrioStd.lean`）。
  - 順序を保ち、順序を反映し、単射である（`omegaIndexMatrix_lt_iff`、`omegaIndexMatrix_injective`、`Trans/BMS/TrioMono.lean`）。表の「拡張ブーフホルツ ψ → トリオ数列」の単射性が ✅ になった。
  - 規則 1〜10（`e0 <= a < Λ`）を書き起こした（`Trans/BMS/TrioRules.lean`）。`#guard` 875 個で照合した（`TrioRulesSheet.lean`）。813 行のうち、標準形でない 28 行を除く 785 行で、744 行が対応表と一致し、41 行は参照プログラムの出力と一致するが対応表とは違う。
  - 共終性：koteitan/trio の `trio_cofinality` とその依存 16 ファイルを `Trans/BMS/TrioCof/` に移し、この文庫の BMS への橋を証明した（`trio_cofinal`、`trioStd_cofinal`、`Trans/BMS/TrioCofinal.lean`）。
  - ペア数列 → 拡張ブーフホルツ ψ の「展開を保つ」「展開と可換」は偽（`Trans/PSS/Expansion.lean`、`pairToExb_not_preserves`、`pairToExb_not_commutes`）。反例は生成元 `(0,0)(1,1)` の `[0]`。
- DBMS の `r` 行 → `r + 1` 行を証明した（2026-09-23、`Trans/DBMS/ZeroRow.lean`）。全射でないことも証明し、表のマスは ✅✅✅✅❌✅(*3)。BMS の同じ写像の全射性も同じ方法で反証できると分かった（plan に追加）。
- トリオの共終性を ψ の項の側で述べ直した（2026-09-23、`Trans/BMS/TrioCofPsi.lean`）。極限の `a` では両方向に共終。後続の `a` は plan に残した。
- 規則 1〜10 の書き起こしが `e0` 未満で `trioMatrix` と一致することを、深さ 201 以下で証明した（`TrioRulesE0.lean`）。導出された `==` が不透明で証明できなかったので、`predBeta` をパターン照合で書き直した（動作は同じ）。燃料 200 では深さ 203 の塔で食い違う。
- 41 行を判定した（`TRIO-SHEET-41-ja.md`）。書き起こしの誤りは無い。規則が正しい 17 行、表が正しい 22 行、未決 1、対象外 1。
- BMS の `r` 行 → `r+1` 行が全射でないことを証明した（`ZeroRowSurj.lean`）。表のマスに注 (*4)。
- 2 行の DBMS の順序数への翻訳写像を作り、6 つの性質を全部証明した（`Trans/DBMS/TwoRow.lean`）。README の行を「2 行の DBMS」（全部 ✅）と「3 行以上の DBMS」に分けた。
- ペア数列の 1 手は ψ の側の 1 手以上に写ることを証明した（`Trans/PSS/Steps.lean`、`Goals/PairReach.lean`）。
- トリオの後続の場合の共終性（`TrioSucc.lean`）と、燃料を深さで与えた規則 1〜10 がすべての `a < e0` で一致すること（`TrioRulesFuel.lean`）を証明した（2026-09-23）。
- 規則 1〜10 を 4 か所直した（`TrioRules2.lean`、2026-09-23）。表が正しい 22 行で表の行列を出し、ほかの標準形の行は変えない。koteitan/trio の `tools/probe_eps_range.py` にも同じ修正が要る。
- 行 3480 を判定した（`TrioRow3480.lean`、2026-09-23）。ラベルは正しく、表も規則も誤り。正しい行列 `c2` は標準形であることを Lean で証明した。
- ペア数列の 1 手が写る ψ の手数に上限が無いことを証明した（`PSS/StepBound.lean`、`Goals/PairStepBound.lean`）。数値で見つけた族は `[2]` の展開、証明した族は `[0]` の展開で、別の族である。
- DBMS の階数を、何行でもブロックの中身の階数に帰着した（`DBMS/Blocks.lean`）。3 行では最初の生成元まで求めた（`DBMS/ThreeRow.lean`）。中身の系 `C_3` は 3 行の BMS の標準形に含まれない（yaBMS）。
- 添字が 0 か 1 だけの項で、トリオの写像が標準形を出し順序を保つことを証明した（`TrioTree*.lean`）。規則の燃料 200 のため、深さ 206 と 207 の二つの項が同じ行列になる。`ofTerm` は `p0(W+1)` を `e0^{e0^w}` と読み、表の `e0·w` の行と合わない。
- 行 4746、4747、4752、4753 で表が正しいことを確かめた（`TrioSheet41Confirm.lean`）。行 3552 の書かれたラベルの行列を修正 E で直した（`TrioRules3.lean`）。41 行のノートの「より上に来る」は誤りで、「より下に来る」に直した。
- 中身の系 `C_3` の生成元が BMS の生成元の持ち上げであることを証明し、3 行の DBMS と BMS が同じ順序数になるという予想を立てた（`DBMS/ThreeRowLift.lean`）。数値では約 600 個の標準形で反例なし。
- 標準形のブロックの並びの必要条件を証明した（`DBMS/BlocksStd.lean`）。3 行で 8 列以下の 43597 通りでは、標準形と「中身が辞書式に減る」が一致した。
- 修正 N（`TrioRulesNonLast.lean`）：塔の範囲で最後でない葉をすぐに格上げし、`W_{W_W}+W_{W_2}+1` の順序を直した。規則の版が 4 つになったので、まとめる項目を plan に足した。
