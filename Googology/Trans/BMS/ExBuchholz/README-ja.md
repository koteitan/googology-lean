[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/BMS/ExBuchholz

BMS ↔ 拡張ブーフホルツ ψ。行列の階数を ψ の値で与える（1 行、ε 数、ζ、ペア数列: 階数 = 1 + val、`PSS/`）。ψ をトリオ数列に写す規則（`Trio/`）。

- [PSS/](PSS/README-ja.md): 2 行（ペア数列）。
- `Trio/`: 3 行（トリオ数列）。規則の直しごとに、そこに説明 `TRIO-*-ja.md` がある。

## ファイル

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| BMS、拡張ブーフホルツ ψ | `Calibrate.lean` | — | `p0(W)` 未満が添字全部 0 とちょうど一致すること。よって読み取りはそこの標準形を全部拾う |
| BMS、拡張ブーフホルツ ψ | `Eps0.lean` | — | **1 行が名指すのは `e0` 未満の順序数ちょうどであること**。そこで `val` は全射で、証明は Cantor 標準形。`p0(W)` は `e0` である。同じ構成を `e1` まで伸ばしてある。先頭項が `p0(W + B)` になる |
| BMS、拡張ブーフホルツ ψ | `EpsN.lean` | — | **`val` が全ての `e_n` 未満へ、したがって `e_w` 未満へ全射であること**。`n` についての帰納法で、段は `e1` の構成そのものである。`W·n + B` を項にして、先頭項を `p0(W·(n+1) + B)` にする。極限が `p0(p1(1))` である |
| BMS、拡張ブーフホルツ ψ | `Arg.lean`, `EpsBig.lean` | — | **`val` が `e_{e0}` 未満へ全射であること**。そこでは全単射である。`mu < e0` の全てで `W·mu` を名指す項を Cantor 標準形から作り（`W·w^e` は `p1(e)`）、その上で同じ先頭項の構成を `d < e0` の全段で回す |
| BMS、拡張ブーフホルツ ψ | `Zeta.lean` | — | **`val` が `z0` 未満へ全射であること**。しかも標準形はただ一つである。引数の項と値の項を一本の帰納法で作るので、指数自身が e 数でも、その添字が与える段で名指される。`C_0(Λ)` への全射という一般の形は `Notation.ExBuchholz.Term.Vals_eq` である。これらのファイルはどの項がどの順序数を名指すかを言い、一般の定理はそれを言わない |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/Trio.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `p0(W_a)` から trio 行列への写像（`a < e0`）。[アルゴリズム](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md)から転記し、[対応表](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/1/README-en.md)で検算した。定理ではなく転記と `#guard` である |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioStd.lean` | — | **trio 行列が標準形であること**（`a < e0`）。`p0(W_a)` の trio 行列は、生成元から有限回の展開で届く 3 行の配列の成分である（`trioMatrix_std`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioMono.lean` | — | **trio の写像が順序を保ち、順序を反映すること**（`a < e0`、列の辞書式順序。`omegaIndexMatrix_lt_iff`）。したがって単射である（`omegaIndexMatrix_injective`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioRules.lean`、`Trio/TrioRulesSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `e0 <= a < Λ` の規則 1〜10 の書き起こし（`TrioRules.trioMatrixL`）と、`#guard` 875 個の照合。定理ではなく転記と `#guard` である |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioRulesE0.lean` | — | **規則 1〜10 の書き起こしは `e0` 未満で `trioMatrix` と一致する**（深さ 201 以下の標準形の項。`trioMatrixL_eq_trioMatrix'`）。燃料 200 ではすべての `a < e0` には足りず、深さ 203 の塔で食い違う（`#guard`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioRulesFuel.lean` | — | **燃料を項の深さで与えた規則 1〜10 は、すべての `a < e0` で `trioMatrix` と一致する**（`trioMatrixD_eq_trioMatrix`）。燃料 200 の版は `trioMatrixF_200` で元の `TrioRules.trioMatrixL` と同じ |
| 3 行の BMS | `Trio/TrioSheet41.lean`、[TRIO-SHEET-41-ja.md](Trio/TRIO-SHEET-41-ja.md) | [koteitan/trio](https://github.com/koteitan/trio) | 規則 1〜10 と対応表が食い違う 41 行の判定。どれも書き起こしの誤りではない。規則が正しい 17 行、表が正しい 22 行、未決 1 行、対象外 1 行。`#guard` による較正で、定理ではない |
| 3 行の BMS | `Trio/TrioRules2.lean`、`Trio/TrioRules2Sheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 規則 1〜10 を 4 か所直したもの。表が正しい 22 行で表の行列を出し、ほかの標準形の行は変えない。選んだ 783 個の行列はラベルの順序に並ぶ。`#guard` による較正で、定理ではない |
| 3 行の BMS | `Trio/TrioSheet41Confirm.lean`、[TRIO-SHEET-4746-ja.md](Trio/TRIO-SHEET-4746-ja.md) | [koteitan/trio](https://github.com/koteitan/trio) | 行 4746、4747、4752、4753 で表が正しいことを、順序、写したブロックを足す段、最後の項の段で確かめた。`#guard` による較正で、定理ではない |
| 3 行の BMS | `Trio/TrioRules3.lean`、`Trio/TrioRules3Sheet.lean`、[TRIO-SHEET-FIXES-ja.md](Trio/TRIO-SHEET-FIXES-ja.md) | [koteitan/trio](https://github.com/koteitan/trio) | 修正 E：行 3552 の書かれたラベル（`u = W+1`、段 `w`）の行列を直した。新しい行列は標準形で順序も合い、表のほかの行は変わらない。`#guard` による較正で、定理ではない |
| 3 行の BMS | `Trio/TrioRulesNonLast.lean`、`Trio/TrioRulesNonLastSheet.lean`、[TRIO-NONLAST-LEAF-ja.md](Trio/TRIO-NONLAST-LEAF-ja.md) | [koteitan/trio](https://github.com/koteitan/trio) | 修正 N：塔の範囲で、最後でない葉をすぐに格上げする。`W_{W_W}+W_{W_2}+1 < W_{W_W}·2` になり、表の行は変わらない。`#guard` による較正で、定理ではない |
| 3 行の BMS | `Trio/TrioRulesAll.lean`、`Trio/TrioRulesAllSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 修正 A〜E と N をまとめた規則 1〜10。修正ごとの版の検査をすべて通り、選んだ 784 個の行列の順序も合う。`#guard` による較正で、定理ではない |
| 3 行の BMS | `Trio/TrioFixMulNormalize.lean`、`Trio/TrioFixMulNormalizeSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `TrioRulesAll` への修正。`mul` と `power` は `w^原子` を原子と書く（`mkExp`）。`==` の判定はパターンにした。変わるのは行 4369 の書かれたラベルだけ（`M(W_W)` になる）。シートの検査はすべて通り、手で作った `w^原子` の 22 個のラベルで順序の不一致は 62 から 0 に減る（[TRIO-FIX-MUL-NORMALIZE-ja.md](Trio/TRIO-FIX-MUL-NORMALIZE-ja.md)） |
| 3 行の BMS | `Trio/TrioFixFuel.lean`、`Trio/TrioFixFuelE0.lean`、`Trio/TrioFixFuelSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `TrioRulesAll` への修正。燃料 200 を `max 200 (a の深さ)` にする。深さ 200 までは何も変わらない（`MD_eq_MAll`）。`e0` より下では、どの深さでも順序を保ち単射（`trioMatrixLD_lt_iff`、`trioMatrixLD_injective`）。深さ 206 と 207 の衝突は消えた（[TRIO-FIX-FUEL-ja.md](Trio/TRIO-FIX-FUEL-ja.md)） |
| 3 行の BMS | `Trio/TrioFixLastLeaf.lean`、`Trio/TrioFixLastLeafSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `TrioRulesAll` への修正（Fix L）。最後の葉 `W_p` で `p` が塔のレジームの上端でないとき、ブロックを持ち上げた写しを付ける（場合 L、K、K'、D）。`W_{W_W}` の後の 6 つの目標はどれも標準形。最後の葉の 151 ラベルで、不一致は 555 → 0、非標準は 43 → 0。シートの行は変わらない（[TRIO-FIX-LASTLEAF-ja.md](Trio/TRIO-FIX-LASTLEAF-ja.md)） |
| 3 行の BMS | `Trio/TrioFixStretch.lean`、`Trio/TrioFixStretchSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `TrioRulesAll` への修正（Fix S）。`W_w·W+W_2` から `W_w·W·2` までの区間で、`W` を名指す葉の後に置かれたユニットに葉の値と持ち上げた写しを与える（S1〜S5）。シートの行 3480、3481、3482 が変わり、標準形になる（3480 は `c2`）。区間の 69 ラベルはすべて標準形（前は 54 個が非標準）、順序の不一致は 0（[TRIO-FIX-STRETCH-ja.md](Trio/TRIO-FIX-STRETCH-ja.md)） |
| 3 行の BMS | `Trio/TrioFixOfTerm.lean`、`Trio/TrioFixOfTermSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 項の読み方の修正。`p_a(b_hi + b_lo)` を `w^(P + b_lo)` と読むので、`p0(W+1)` は `e0·w` になる（シートの行 2158）。シートのラベルを持つ 42 個の標準形の項で、行列はすべて正しい（古い読み方では 25 個）。新しい写像では `TrioTree` の順序の定理が成り立たない（`not_trioMatrixLFix_lt_iff`。`strip` が `w^{e0·w}` を誤って組むため）（[TRIO-FIX-OFTERM-ja.md](Trio/TRIO-FIX-OFTERM-ja.md)） |
| 3 行の BMS | `Trio/TrioFixStrip.lean`、`Trio/TrioFixStripTree.lean`、`Trio/TrioFixStripSheet*.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 修正 `ofterm` への修正。規則 1 の `strip` は `w^{e0·w}` を `p0(W+p0(W+1))` として組む。木の写像 `trioE2` は、添字が 0 と 1 の項で順序を保ち、単射で、標準形を与える（`trioE2_lt_iff`、`trioE2_injective`、`trioE2_std`）。規則の写像は `CalibSt` が成り立てばそれと一致する（未解決。9,782 項でずれ 0）。Sheet は別のライブラリ `GoogologySheets` にある（[TRIO-FIX-STRIP-ja.md](Trio/TRIO-FIX-STRIP-ja.md)） |
| 3 行の BMS | `Trio/TrioFixStripCalib*.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 修正 `strip` の規則の写像は、添字が 0 と 1 で読みの深さ `rdT` が 100 以下の項で、木の写像 `trioE2` と一致する（`trioMatrixLSt_eq_trioE2`）。よってそこでは順序を保ち、単射で、標準形を与える（`trioMatrixLSt_lt_iff`、`trioMatrixLSt_std`）。深さの上限なしでは偽：燃料 200 のため、塔 `T_202` と `T_203` が同じ行列になる（`not_calibSt`、`trioMatrixLSt_not_injective`） |
| 3 行の BMS | `Trio/TrioFixU.lean`、`Trio/TrioFixUSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `TrioRulesAll` への修正（Fix U）。レベル 1 で `u = W+k`、`w` が `p` で始まる `p_u(w)` の規則 9 を置き換える。範囲の中の 562 ラベルで、非標準の行列は 337 → 0。主張する範囲は広すぎる（規則 9 そのものが誤る反例が 3 つ）（[TRIO-FIX-U-ja.md](Trio/TRIO-FIX-U-ja.md)） |
| 3 行の BMS | `Trio/TrioFixU2.lean`、`Trio/TrioFixU2Sheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 修正 U への修正（Fix U2）。規則 9 は、上げの印を親の列から離さない（Fix K）。レベル `L >= 2` で `W_W < w <= W_{W_L}` のときは、新しいずらしの行を使う。2,097 個の試しのラベルで、規則 9 の誤りは 41 → 0、570 → 22。非標準になるラベルは無い（[TRIO-FIX-U2-ja.md](Trio/TRIO-FIX-U2-ja.md)） |
| 3 行の BMS | `Trio/TrioFixNonLastOther.lean`、`Trio/TrioFixNonLastOtherSheet.lean` | [koteitan/trio](https://github.com/koteitan/trio) | `TrioRulesAll` への修正。塔以外の範囲の、最後でない葉（変更 1〜3、Fix G と M）。`W_{W_w}`、`W_{W_{w+1}}`、`W_{W_2}`、`W_{W_W}`、`W_W` の後の 5 つの族で、順序の不一致は数千から 0〜3 に減る。族の外では Fix M、Fix G、変更 1 が、正しかった組を壊す（例：`W_{W_2}+W_w+W` と `W_{W_2}+W+w`）。docstring を見よ |
| 3 行の BMS | `Trio/TrioFixNonLastOther2.lean`、`Trio/TrioFixNonLastOther2Sheet*.lean` | [koteitan/trio](https://github.com/koteitan/trio) | 修正 nonlast-other への修正。Fix M、Fix G、変更 1 は、名指すレベルの葉が下の上端と離れているときだけ働く（変更 1′、G′、M′）。検証で見つかった 9 つの後退はすべて消え、較正した 5 つの族の行列は変わらない。3,387 ラベルで、`TrioRulesAll` の標準形が非標準になるものは無い。`W_{W_{w+2}}` などの後では、まだ順序の違う組が残る（[TRIO-FIX-NONLAST2-ja.md](Trio/TRIO-FIX-NONLAST2-ja.md)） |
| 3 行の BMS | `Trio/TrioRow3480.lean`、[TRIO-ROW-3480-ja.md](Trio/TRIO-ROW-3480-ja.md) | [koteitan/trio](https://github.com/koteitan/trio) | 行 3480（`W_w·W+W_3`）の判定。表も規則も誤りで、正しい行列 `c2` は標準形（`trioStdL_c2`）で、`M(W_w·W+W_w)[1]` に等しい |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioTree.lean`、`Trio/TrioTreeStd.lean`、`Trio/TrioTreeRules.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **添字が 0 か 1 だけの可算な標準形の項**（どれも `p0(W_2)` 未満）で、構造的な写像 `trioE` は標準形を出し（`trioE_std`）、順序を保ち、順序を反映する（`trioE_lt_iff`）。深さ 200 以下では規則 1〜10 は `trioE` と一致する（`trioMatrixL_eq_trioE`）。200 はぎりぎりで、深さ 206 と 207 の二つの項が同じ行列になる（`#guard`） |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioCofPsi.lean` | — | **trio の展開の共終性を ψ の項で述べたもの**（`a < e0`）。trio 行列は trio の断片に入る（`trioStdL_omegaIndexMatrix`）。`p0(W_b) < p0(W_a)`（またはその `val`）なら `M(b) ≤ M(a)[k]` となる `k` がある（`trioPsi_cofinal`、`trioPsi_cofinal_val`）。極限の `a`（`dom a = w`）では `p0(W_a)[n] = p0(W_{a[n]})` で、列 `M(a)[k]` と `M(a[n])` は互いに共終であり、各 `M(a)[k]` はある `M(a[n])` の先頭部分である（`trioPsi_fs`、`trioPsi_expand_prefix`）。後続の `a` では基本列の項 `p0(p_a(⋯))` が写像の定義域の外にある |
| 3 行の BMS、拡張ブーフホルツ ψ | `Trio/TrioSucc.lean` | — | **後続の `a = b + 1` での共終性**。`p0(W_a)[n] = p0(p_b^{n+1}(0))` で、その trio 行列 `towerMatrix b n` と `M(a)[k]` は互いに共終（`trioPsi_fs_succ`）。`b = 0` と `b` が後続のときは `towerMatrix` は `M(a)` の展開そのもの |
| BMS、拡張ブーフホルツ ψ | `RankVal.lean` | — | **系の階数が項の値であること**。定義の違う二つの測度が同じものであること。そのうえで、読み取りが無い所の階数を計算する。2 行の生成元、後続、ブロックの繰り返し、族 `(0,0)(1,1)(1,0)^k` |
| BMS、拡張ブーフホルツ ψ | `Prim.lean` | `StepHom` | 原始数列系を `Rewrite` として与え、停止することとその順序数 |
| BMS、拡張ブーフホルツ ψ | `Cofinal.lean` | — | `p0(W)` 未満で項が `X[0] < X[1] < ⋯` の上限であること |
| BMS、拡張ブーフホルツ ψ | `Bms.lean` | `StepHom` | **1 行の BMS が名指す順序数**、それが `p0(W)` 未満であること、翻訳による 1 行の停止性 |
| BMS、拡張ブーフホルツ ψ | `Equiv.lean` | `Equiv` | **原始数列系と `p0(W)` 未満の標準形は、一つの系の二通りの書き方である** |
| BMS、拡張ブーフホルツ ψ | `Reach.lean` | — | **標準 1 行行列とは、項が標準形である行列のことちょうどである** |
| BMS、拡張ブーフホルツ ψ | `Commute.lean` | いずれ `StepHom` | 読み取りが展開を `[ ]` に変えること、添字の付け替え `N ↦ N + 1` を込めて |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/Expand.lean`、`PSS/Terms.lean`、`PSS/Rank.lean` | — | **ペア数列の順序数への翻訳写像**。koteitan/pss-proof の `Trans` を通す。その展開は `expand2L` である（`oper_succ_eq_expand2L_of_ctps`）。その Buchholz 項は `p0(W_w)` 未満の標準的な拡張ブーフホルツ項の上へ写る（`toTerm_bijOn_TransRange`）。ペア数列の階数はその項の `1 + val` で（`rank_pairL_eq`）、値の範囲は `p0(W_w)` 未満の順序数全部である（`range_pairOrd`）。詳しくは [PSS/README-ja.md](../PoR/PSS/README-ja.md) にある |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/Expansion.lean` | — | **ペア数列 → 拡張ブーフホルツ ψ は展開を保たないこと**。生成元 `(0,0)(1,1)` の `[0]` は `(0,0)` で、`p0(W_1)` の基本列の項は `1` にならない（`pairOrdTerm_step_ne_fs`） |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/Steps.lean`、`../../../Goals/PairReach.lean` | — | **1 手は ψ の側の 1 手以上に写る**。「何手かで届く」は写像で両方向に保たれる（`pairToExbOT_transGen_iff`、`pairToExb_transGen_iff`）。`(0,0)(1,1)[0]` は `p0(W_1) →[0] w →[1] 1` |
| BMS（ペア数列）、拡張ブーフホルツ ψ | `PSS/StepBound.lean`、`../../../Goals/PairStepBound.lean` | — | **ψ の手数に上限は無い**（`pairToExb_steps_unbounded`）。`(0,0)...(p,p)(p+1,p)[0]` は `p0(p_p(p_p(0)))` から `p0(p_p(0))` へちょうど `p+1` 手（`pairToExb_min_steps`）。どの添字を選んでも、基本列の 1 手で一番右の道の添字 `lastSub` がちょうど 1 減る（`lastSub_fs_idx`） |
| BMS、拡張ブーフホルツ ψ | `Tables.lean`、`../../DBMS/ExBuchholz/Tables.lean` | `StepHom` | README の表の小さなセル。原始数列の順序は値の順序であること、1 行の翻訳写像が階数を保つこと、原始数列がペア数列の中へ単射で入ること |
| BMS、拡張ブーフホルツ ψ | `Basic.lean` | いずれ `Sim` | 1 行の場合の読み取り `read`、その項が標準形になるのは降順のときちょうどであること、そしてそれが全単射であること |
