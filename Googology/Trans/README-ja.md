[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans

具体的な翻訳。2 つの系を同時に import する唯一の層。

## 規則

対 `{X, Y}` には**ファイルを 1 つ**だけ置く。名前順で先に来る方の下に置く。

```
Trans/BMS/DBMS.lean     BMS と DBMS に関する全部
Trans/BMS/Y.lean        BMS と Y に関する全部
```

方向ごとではなく、対ごとに 1 ファイルである。両方向の模倣と、あれば `Equiv` を
同じ場所に置く。そうしないと `Equiv` の置き場所が決まらず、2 つの方向が
離れていく。どちら側からでも引けるように、下に索引を置く。

系は全部 [Notation](../Notation/README-ja.md) にあるので、巨大数の系から
証明論の系への翻訳も、他の対と何も変わらない。名前順で先に来る方の下に置く。
`Trans/BMS/OTB.lean`。

対ひとつにファイルひとつは出発点であって上限ではない。育った対は — `BMS` と
拡張ブーフホルツ ψ は数ファイルに渡る — ディレクトリを保ったまま、何を証明して
いるかで分ける。下の索引が各部を並べる。系ひとつだけについてのファイルも、翻訳が
それを使うために要るなら同じディレクトリに置き、自分自身との対として索引に載せる。

## どれを作るか

仕事が済む範囲で一番弱いものを選ぶ。

| 構造 | 要求 | 得られるもの |
|---|---|---|
| `Sim` | 一歩が一歩に写る | 整礎性と停止性が移る |
| `StepHom` | 展開と可換、＋停止状態の対応 | `Sim` になる |
| `Equiv` | 互いに逆な `Sim` | 両側が同値 |
| `OrdHom` | 順序を保つだけ | 整礎性が移る |

`StepHom` は括弧の番号を付け替える `reindex : Nat → Nat` を持つ。付け替えない
なら `id` を入れる。

## 較正は定理ではない

参照実装との一致は有限個の検査（`#guard`、`decide`）であって、全入力についての
証明ではない。別ファイルに置き、上の定理と同列に読まれないようにする。

## 索引

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| BMS 自身 | `BMS/OneRow.lean` | — | 1 行の展開が原始数列の規則であること: 最初の `p` 個を残し、続く `s` 個を `N + 1` 回繰り返す |
| BMS 自身 | `BMS/Rows.lean` | — | 親を名指せば bad root が決まること。行数によらない |
| BMS 自身 | `BMS/Entries.lean` | — | 配列とその成分列が同じ展開をすること |
| BMS 自身 | `BMS/TwoRow.lean` | — | 2 行の展開: `m₀` は 0 か 1 で、1 のとき行 0 に加算が入る |
| BMS 自身 | `BMS/Anc.lean` | — | 行 0 の祖先関係を成分列から読み、計算できる形にして `BM4.anc` と一致することを示す |
| BMS 自身 | `BMS/EntriesR.lean` | — | **BMS の展開を行数によらず成分列の上に書き、それが `BM4.expand` であること** — だから走る |
| BMS 自身 | `BMS/AllL.lean` | `Sim` | 標準形かどうかによらず**全**行列上の規則を、走る系として与え、標準形はその中に置く |
| BMS 自身 | `BMS/Zero.lean` | — | 下に 0 の行を足しても何も変わらないこと。2 行の規則がそこでは 1 行の規則になる |
| BMS 自身 | `BMS/Embed.lean` | `StepHom` | **原始数列系がペア数列系の中に入ること** |
| BMS 自身 | `BMS/ZeroRow.lean` | `StepHom`, `Sim` | **それが行数によらず成り立つこと**。`r + 1` 行が `r + 2` 行の中に、`s ≥ r` なら `s + 1` 行の中に入る |
| BMS どうし | `BMS/ZeroRowSurj.lean` | — | BMS の `r` 行 → `r + 1` 行は全射でない。生成元 `(0,0)(1,1)` は像に無い（`bmsToSucc_not_surjective`） |
| BMS 自身 | `BMS/Append.lean` | — | **展開が最後のブロックしか見ないこと**。行 `0` の成分が `0` の列がブロックの始まりで、親はそこを越えて戻らない |
| BMS 自身 | `BMS/Entries2.lean` | — | **2 行の展開を成分列の上に書き、それが `BM4.expand` であること、そして走らせれば止まること** |
| BMS 自身 | `BMS/Pair.lean` | — | ペア数列系を、ステップが走る `Rewrite` として与え、生成元も付ける |
| BMS 自身 | `BMS/Agree.lean` | — | 1 行・2 行・一般の規則が一致すること。一般の系も生成元付きの `Rewrite` にする |
| BMS 自身 | `BMS/Same.lean` | `Equiv` | 一般の系の 1 行が原始数列系**そのもの**、2 行がペア数列系そのものであること |
| BMS 自身 | `BMS/Cut.lean` | — | ブロック再帰 `expandL` が教科書どおりの規則であること: 最後の列を落とし、悪い部分を `N + 1` 回繰り返す |
| BMS、拡張ブーフホルツ ψ | `BMS/Calibrate.lean` | — | `p0(W)` 未満が添字全部 0 とちょうど一致すること。よって読み取りはそこの標準形を全部拾う |
| BMS、拡張ブーフホルツ ψ | `BMS/Eps0.lean` | — | **1 行が名指すのは `e0` 未満の順序数ちょうどであること**。そこで `val` は全射で、証明は Cantor 標準形。`p0(W)` は `e0` である。同じ構成を `e1` まで伸ばしてある。先頭項が `p0(W + B)` になる |
| BMS、拡張ブーフホルツ ψ | `BMS/EpsN.lean` | — | **`val` が全ての `e_n` 未満へ、したがって `e_w` 未満へ全射であること**。`n` についての帰納法で、段は `e1` の構成そのものである。`W·n + B` を項にして、先頭項を `p0(W·(n+1) + B)` にする。極限が `p0(p1(1))` である |
| BMS、拡張ブーフホルツ ψ | `BMS/Arg.lean`, `BMS/EpsBig.lean` | — | **`val` が `e_{e0}` 未満へ全射であること**。そこでは全単射である。`mu < e0` の全てで `W·mu` を名指す項を Cantor 標準形から作り（`W·w^e` は `p1(e)`）、その上で同じ先頭項の構成を `d < e0` の全段で回す |
| BMS、拡張ブーフホルツ ψ | `BMS/Zeta.lean` | — | **`val` が `z0` 未満へ全射であること**。しかも標準形はただ一つである。引数の項と値の項を一本の帰納法で作るので、指数自身が e 数でも、その添字が与える段で名指される。`C_0(Λ)` への全射という一般の形は `Notation.ExBuchholz.Term.Vals_eq` である。これらのファイルはどの項がどの順序数を名指すかを言い、一般の定理はそれを言わない |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/Trio.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `p0(W_a)` から trio 行列への写像（`a < e0`）。[アルゴリズム](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md)から転記し、[対応表](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/1/README-en.md)で検算した。定理ではなく転記と `#guard` である |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioStd.lean` | — | **trio 行列が標準形であること**（`a < e0`）。`p0(W_a)` の trio 行列は、生成元から有限回の展開で届く 3 行の配列の成分である（`trioMatrix_std`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioMono.lean` | — | **trio の写像が順序を保ち、順序を反映すること**（`a < e0`、列の辞書式順序。`omegaIndexMatrix_lt_iff`）。したがって単射である（`omegaIndexMatrix_injective`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioRules.lean`、`BMS/TrioRulesSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `e0 <= a < Λ` の規則 1〜10 の書き起こし（`TrioRules.trioMatrixL`）と、`#guard` 875 個の照合。定理ではなく転記と `#guard` である |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioRulesE0.lean` | — | **規則 1〜10 の書き起こしは `e0` 未満で `trioMatrix` と一致する**（深さ 201 以下の標準形の項。`trioMatrixL_eq_trioMatrix'`）。燃料 200 ではすべての `a < e0` には足りず、深さ 203 の塔で食い違う（`#guard`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioRulesFuel.lean` | — | **燃料を項の深さで与えた規則 1〜10 は、すべての `a < e0` で `trioMatrix` と一致する**（`trioMatrixD_eq_trioMatrix`）。燃料 200 の版は `trioMatrixF_200` で元の `TrioRules.trioMatrixL` と同じ |
| 3 行の BMS | `BMS/TrioSheet41.lean`、[TRIO-SHEET-41-ja.md](BMS/TRIO-SHEET-41-ja.md) | [koteitan/trio](https://github.com/koteitan/trio) | 規則 1〜10 と対応表が食い違う 41 行の判定。どれも書き起こしの誤りではない。規則が正しい 17 行、表が正しい 22 行、未決 1 行、対象外 1 行。`#guard` による較正で、定理ではない |
| 3 行の BMS | `BMS/TrioRules2.lean`、`BMS/TrioRules2Sheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 規則 1〜10 を 4 か所直したもの。表が正しい 22 行で表の行列を出し、ほかの標準形の行は変えない。選んだ 783 個の行列はラベルの順序に並ぶ。`#guard` による較正で、定理ではない |
| 3 行の BMS | `BMS/TrioRow3480.lean`、[TRIO-ROW-3480-ja.md](BMS/TRIO-ROW-3480-ja.md) | [koteitan/trio](https://github.com/koteitan/trio) | 行 3480（`W_w·W+W_3`）の判定。表も規則も誤りで、正しい行列 `c2` は標準形（`trioStdL_c2`）で、`M(W_w·W+W_w)[1]` に等しい |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioTree.lean`、`BMS/TrioTreeStd.lean`、`BMS/TrioTreeRules.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **添字が 0 か 1 だけの可算な標準形の項**（どれも `p0(W_2)` 未満）で、構造的な写像 `trioE` は標準形を出し（`trioE_std`）、順序を保ち、順序を反映する（`trioE_lt_iff`）。深さ 200 以下では規則 1〜10 は `trioE` と一致する（`trioMatrixL_eq_trioE`）。200 はぎりぎりで、深さ 206 と 207 の二つの項が同じ行列になる（`#guard`） |
| 3 行の BMS | `BMS/TrioCof/`、`BMS/TrioCofinal.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **trio 数列の展開の共終性**。koteitan/trio の `trio_cofinality` とその依存 16 ファイルを移し、この文庫の BMS の展開と同じであることを証明した（`expandRL_toL`）。標準形の `b < a` には、`b ≤ a[k]` となる `k` がある（`trio_cofinal`、`trioStd_cofinal`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioCofPsi.lean` | — | **trio の展開の共終性を ψ の項で述べたもの**（`a < e0`）。trio 行列は trio の断片に入る（`trioStdL_omegaIndexMatrix`）。`p0(W_b) < p0(W_a)`（またはその `val`）なら `M(b) ≤ M(a)[k]` となる `k` がある（`trioPsi_cofinal`、`trioPsi_cofinal_val`）。極限の `a`（`dom a = w`）では `p0(W_a)[n] = p0(W_{a[n]})` で、列 `M(a)[k]` と `M(a[n])` は互いに共終であり、各 `M(a)[k]` はある `M(a[n])` の先頭部分である（`trioPsi_fs`、`trioPsi_expand_prefix`）。後続の `a` では基本列の項 `p0(p_a(⋯))` が写像の定義域の外にある |
| 3 行の BMS、拡張ブーフホルツ ψ | `BMS/TrioSucc.lean` | — | **後続の `a = b + 1` での共終性**。`p0(W_a)[n] = p0(p_b^{n+1}(0))` で、その trio 行列 `towerMatrix b n` と `M(a)[k]` は互いに共終（`trioPsi_fs_succ`）。`b = 0` と `b` が後続のときは `towerMatrix` は `M(a)` の展開そのもの |
| BMS、拡張ブーフホルツ ψ | `BMS/RankVal.lean` | — | **系の階数が項の値であること**。定義の違う二つの測度が同じものであること。そのうえで、読み取りが無い所の階数を計算する。2 行の生成元、後続、ブロックの繰り返し、族 `(0,0)(1,1)(1,0)^k` |
| BMS、拡張ブーフホルツ ψ | `BMS/Prim.lean` | `StepHom` | 原始数列系を `Rewrite` として与え、停止することとその順序数 |
| BMS、拡張ブーフホルツ ψ | `BMS/Cofinal.lean` | — | `p0(W)` 未満で項が `X[0] < X[1] < ⋯` の上限であること |
| BMS、拡張ブーフホルツ ψ | `BMS/Bms.lean` | `StepHom` | **1 行の BMS が名指す順序数**、それが `p0(W)` 未満であること、翻訳による 1 行の停止性 |
| BMS、拡張ブーフホルツ ψ | `BMS/Equiv.lean` | `Equiv` | **原始数列系と `p0(W)` 未満の標準形は、一つの系の二通りの書き方である** |
| BMS、拡張ブーフホルツ ψ | `BMS/Reach.lean` | — | **標準 1 行行列とは、項が標準形である行列のことちょうどである** |
| DBMS 自身 | `DBMS/Entries.lean` | — | 行数によらず DBMS を成分列の上に置き、生成元も付け、停止することも示す |
| DBMS、拡張ブーフホルツ ψ | `DBMS/OneRow.lean` | `StepHom` | 1 行の DBMS についての同じこと。1 行では生成元が BM4 と一致する。どの行列が標準形かも含む |
| DBMS、BMS（原始数列） | `DBMS/OneRowL.lean` | `StepHom`、`Equiv` | **行列の上の 1 行の DBMS**（`dbmsL1`）。配列は成分によってこの系の上へ写る。この系は原始数列の系そのものである。その順序数への写像は単射で、`e0` 未満の順序数全部に全射、階数と一致し、順序を保つ |
| DBMS どうし | `DBMS/ZeroRow.lean` | `StepHom`、`Sim` | **DBMS の `r` 行が `r + 1` 行の中に入ること**。下に 0 の行を足す写像は、標準形に入り、括弧の番号を変えずに展開と可換で、単射で、階数を保つ（`dbmsL_homSucc`、`rank_dbmsL_homSucc`）。全射ではない（`dbmsToSucc_not_surjective`） |
| DBMS、BMS（ペア数列）、拡張ブーフホルツ ψ | `DBMS/TwoRowBlock.lean`、`DBMS/TwoRow.lean` | `Eval` | **2 行の DBMS の順序数への翻訳写像**。標準形は `(0,0)` で始まるブロックの並びで、各ブロックの残りはペア数列（`dreach2_iff_dform`）。値は `w^o(M_0) + w^o(M_1) + ...`（`dbmsL2OrdEval`）。単射、`p0(W_w)` 未満への全射、展開で下がる、階数と一致、順序を保つ（`dbmsL2OrdEval_injective`、`dbmsL2Ord_image`、`rank_dbmsL2_eq`、`ltPS_iff_dOrdL_lt`） |
| DBMS どうし | `DBMS/Blocks.lean`、`DBMS/ThreeRow.lean` | `StepHom`、階数 | **何行でも、DBMS の標準形はブロックの並びで、階数は `w^rank(M_0) + ... + w^rank(M_k)`**（`rank_dbmsL_eq_sum`）。各 `M_i` は生成元 `(0,0,0)(1,1,0)(2,2,1)...` から届く「中身の系」の元。3 行では `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` の階数が `p0(W_w)`（`rank_gen_three_three`）。その先の生成元の階数は未解決 |
| BMS、拡張ブーフホルツ ψ | `BMS/Commute.lean` | いずれ `StepHom` | 読み取りが展開を `[ ]` に変えること、添字の付け替え `N ↦ N + 1` を込めて |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/Expand.lean`、`PSS/Terms.lean`、`PSS/Rank.lean` | — | **ペア数列の順序数への翻訳写像**。koteitan/pss-proof の `Trans` を通す。その展開は `expand2L` である（`oper_succ_eq_expand2L_of_ctps`）。その Buchholz 項は `p0(W_w)` 未満の標準的な拡張ブーフホルツ項の上へ写る（`toTerm_bijOn_TransRange`）。ペア数列の階数はその項の `1 + val` で（`rank_pairL_eq`）、値の範囲は `p0(W_w)` 未満の順序数全部である（`range_pairOrd`）。詳しくは [PSS/README-ja.md](PSS/README-ja.md) にある |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/Expansion.lean` | — | **ペア数列 → 拡張ブーフホルツ ψ は展開を保たないこと**。生成元 `(0,0)(1,1)` の `[0]` は `(0,0)` で、`p0(W_1)` の基本列の項は `1` にならない（`pairOrdTerm_step_ne_fs`） |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/Steps.lean`、`Goals/PairReach.lean` | — | **1 手は ψ の側の 1 手以上に写る**。「何手かで届く」は写像で両方向に保たれる（`pairToExbOT_transGen_iff`、`pairToExb_transGen_iff`）。`(0,0)(1,1)[0]` は `p0(W_1) →[0] w →[1] 1` |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/StepBound.lean`、`Goals/PairStepBound.lean` | — | **ψ の手数に上限は無い**（`pairToExb_steps_unbounded`）。`(0,0)...(p,p)(p+1,p)[0]` は `p0(p_p(p_p(0)))` から `p0(p_p(0))` へちょうど `p+1` 手（`pairToExb_min_steps`）。どの添字を選んでも、基本列の 1 手で一番右の道の添字 `lastSub` がちょうど 1 減る（`lastSub_fs_idx`） |
| BMS、拡張ブーフホルツ ψ | `BMS/Tables.lean`、`DBMS/Tables.lean` | `StepHom` | README の表の小さなセル。原始数列の順序は値の順序であること、1 行の翻訳写像が階数を保つこと、原始数列がペア数列の中へ単射で入ること |
| BMS、拡張ブーフホルツ ψ | `BMS/ExBuchholz.lean` | いずれ `Sim` | 1 行の場合の読み取り `read`、その項が標準形になるのは降順のときちょうどであること、そしてそれが全単射であること |
