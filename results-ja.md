[← Back](README-ja.md) | [English](results.md) | [Japanese](results-ja.md)

# 証明した定理の一覧

名前は `Googology` からの相対で書く。

## 系

| | |
|---|---|
| **バシク行列はどの行数でも停止する** | `Notation.BMS.bms_terminates` |
| **標準形かどうかに関係なく、どんな配列からでも展開は止まる** | `Notation.BMS.terminates_any` |
| だから全配列上の規則も系になり、整礎で階数を持つ | `Notation.BMS.bmsAll`, `Notation.BMS.bmsAll_wf`, `Notation.BMS.bmsAllEval` |
| 成分列の上でも同じこと。こちらはステップが走る | `Trans.BMS.bmsAllL`, `Trans.BMS.bmsAllL_wf`, `Trans.BMS.bmsAllLEval` |
| 原始数列・ペア数列・トリオ数列の停止 | `Notation.BMS.primitive_terminates`、`Notation.BMS.pair_terminates`、`Notation.BMS.trio_terminates` |
| BMS は順序数の測度を持つ | `Notation.BMS.bmsEval` |
| **成分列の上に書いた BMS の展開が `BM4.expand` であること** — 行数によらず、だから走る | `Trans.BMS.entriesR_expand` |
| 1 行・2 行・一般の規則が一つの規則であること | `Trans.BMS.expandRL_one`, `Trans.BMS.expandRL_two` |
| 下に 0 の行を足しても何も変わらないこと。1 行を 2 行の中で見たとき | `Trans.BMS.expand2L_withZero` |
| **原始数列系がペア数列系の中に入ること** | `Trans.BMS.primHomPair`, `Trans.BMS.withZero_std` |
| `bmsL 0` が `bmsL 1` の中に入ること。階層の最初の一段 | `Trans.BMS.bmsL_zero_sim_one` |
| **下に 0 の行を足しても何も変わらないことが、行数によらず成り立つこと** | `Trans.BMS.expandRL_zeroRow` |
| だから `r + 1` 行は `r + 2` 行の中に入る。標準形でも全行列でも | `Trans.BMS.bmsL_homSucc`, `Trans.BMS.bmsAllL_homSucc` |
| それを繰り返して、`r ≤ s` なら `r + 1` 行は `s + 1` 行の中に入る | `Trans.BMS.bmsL_simLe`, `Trans.BMS.bmsAllL_simLe` |
| **0 の行を足しても行列が名指す順序数は変わらないこと** | `Trans.BMS.rank_zeroRow`, `StepHom.rank_map` |
| 成分列の上の系と、その生成元 | `Trans.BMS.prim`, `Trans.BMS.pairL`, `Trans.BMS.bmsL`, `Trans.DBMS.dbmsL1` |
| 一般の系の 1 行が原始数列系、2 行がペア数列系であること | `Trans.BMS.bmsEquivPrim`, `Trans.BMS.pairEquivBms` |
| 生成元から出発した展開列は必ず止まること | `Notation.BMS.bmsStd_terminates`, `Notation.DBMS.dbmsStd_terminates`, `Trans.BMS.bmsLStd_terminates` |
| **整礎性と停止性は同じ条件であること** | `Rewrite.wf_iff_terminates` |
| だからここにある系はどれも整礎で、展開が階数を持つこと | `Trans.BMS.bmsL_wf`, `Trans.BMS.pairL_wf`, `Trans.BMS.prim_wf`, `Trans.BMS.bmsLRankEval` |
| DBMS は同じ規則で生成元だけが違い、やはり停止する | `Notation.DBMS.dbms_terminates`, `Trans.DBMS.dbmsL_terminates` |
| 系としての Y 数列。公式プログラムを書き起こし、213 件の展開で照合した | `Notation.Y.expand`, `Notation.Y.ySys` |
| **Y 数列は整礎で停止し**、順序数の測度を持つ | `Notation.Y.ySys_wf`, `Notation.Y.ySys_terminates`, `Notation.Y.yStd_terminates`, `Notation.Y.yEval` |
| **標準形かどうかによらず合法な列（項が正で先頭が `1`）すべての上でも同じ**。素のリストの上の `expand` についても | `Notation.Y.yLegal_wf`, `Notation.Y.yLegal_terminates`, `Notation.Y.expand_terminates` |
| 合法な列の上で書き起こしは Phyrion 氏の展開に等しい。だから標準形は Phyrion 氏の生成する列と同じで、辞書式順序で整列する | `Notation.Y.expand_eq_numeric`, `Notation.Y.yStd_iff_generated`, `Notation.Y.yStd_strictWellOrder` |

## 拡張ブーフホルツ ψ

| | |
|---|---|
| **標準形は整列する** | `Notation.ExBuchholz.Term.OTLt_wf` |
| 異なる標準形は異なる順序数を名指す | `Notation.ExBuchholz.Term.val_inj_of_OT` |
| 表記系の正しさ。項の順序と順序数の順序が一致する | `Notation.ExBuchholz.Term.val_lt_val` |
| **`C_0(Λ)` の元は全て標準形の値であること**。よって `val` は標準形から `C_0(Λ)` への順序同型で、`p0(Λ)` 未満の順序数はどれもただ一つの標準形が名指す | `Notation.ExBuchholz.Term.Vals_eq`, `Notation.ExBuchholz.Term.valEquiv`, `Notation.ExBuchholz.Term.existsUnique_OT_of_lt_psi_Lam` |
| 標準形が可算順序数を名指すのは、`p0(Λ)` 未満を名指すときちょうどであること | `Notation.ExBuchholz.Term.val_lt_psi_Lam_iff` |
| **可算標準形 `X` の下の標準形は、順序も込めて `val X` 未満の順序数そのものであること**。可算標準形全体は `p0(Λ)` 未満の順序数である。だから `X` の下の順序型は `X` が名指す順序数である | `Notation.ExBuchholz.Term.belowEquiv`, `Notation.ExBuchholz.Term.countableEquiv` |
| 基本列が降下する | `Notation.ExBuchholz.Term.fs_lt` |
| **拡張ブーフホルツ項は停止する** | `Notation.ExBuchholz.Term.exbOT_terminates` |
| 基本列が標準形を保つ（Buchholz 補題 3.3） | `Notation.ExBuchholz.Term.OTFS_thm` |
| **`e0` 未満で `p0(a) = w^a` であること**。`p0(a) <= w^a` は常に成り立つ | `Notation.ExBuchholz.Ord.psi_zero_eq_opow`, `Notation.ExBuchholz.Ord.psi_zero_le_opow` |
| **`p0(W) = e0`** | `Notation.ExBuchholz.Ord.psi_Omega_one` |
| **かつ `e1` 未満で `p0(W + a) = e0·w^a`**。よって `p0(W + 1) = e0·w` | `Notation.ExBuchholz.Ord.psi_Omega_add_eq`, `Notation.ExBuchholz.Ord.psi_Omega_add_one` |
| **かつ `p0(W·2) = e1`**。項 `p0(W+W)` がそれを名指す | `Notation.ExBuchholz.Ord.psi_Omega_two`, `Trans.BMS.val_te1` |
| **かつ有限の全段で `p0(W·(n+1)) = e_n`**。`e_{n+1}` 未満で `p0(W·(n+1) + a) = e_n·w^a` | `Notation.ExBuchholz.Ord.psi_OmegaMul`, `Notation.ExBuchholz.Ord.psi_OmegaMul_add` |
| **かつ `p0(W·w) = e_w`**。`p1(1) = W·w` である | `Notation.ExBuchholz.Ord.psi_Omega_omega`, `Notation.ExBuchholz.Ord.psi_one_one` |
| **かつ `z0` 未満の全ての `g` で `p0(W·(1+g)) = e_g`**。`e_{g+1}` 未満で `p0(W·(1+g) + b) = e_g·w^b` | `Notation.ExBuchholz.Ord.psi_Omega_mul_eps`, `Notation.ExBuchholz.Ord.psi_Omega_mul_add_eps` |
| **かつ `p0(W·z0) = p0(W^2) = z0`** | `Notation.ExBuchholz.Ord.psi_Omega_mul_zeta0`, `Notation.ExBuchholz.Ord.psi_Omega_sq` |
| **かつ同じ梯子が全添字で**。`p_v(W_{v+1}·(1+g)) = e^v_g` | `Notation.ExBuchholz.Ord.psi_OmegaV_mul_eq`, `Notation.ExBuchholz.Ord.psi_OmegaV_mul_eq_nat` |
| `val` が `z0` 未満へ全射であること。一般の定理より前に、項を具体的に作って示したもの。`z0` 自身は `p0(p1(p1(0)))` の値 | `Trans.BMS.exists_OT_of_lt_zeta0`, `Trans.BMS.existsUnique_OT_of_lt_zeta0`, `Trans.BMS.val_tzeta0` |
| `p0(W_a)` から 3 行行列への写像（`a < e0`）。[koteitan/trio](https://github.com/koteitan/trio) から転記し対応表で検算したもので、定理ではない | `Trans.BMS.omegaIndexMatrix` |
| `C_v(a)` の加法的主要な元は `W_v` 未満か collapse であること。`v <= w` で `p_w(d)` が `C_v(b)` に入り、`d` が自分の閉包に入るなら、`d` は `C_v(b)` に入り `b` 未満であること。閉包を `G` で読む Buchholz の補題で、正規形定理はこれに乗る | `Notation.ExBuchholz.Ord.principal_mem_CSet`, `Notation.ExBuchholz.Ord.arg_mem_of_psi_mem`, `Notation.ExBuchholz.Term.G_lt_of_mem_CSet` |
| 標準形がそこへ届くこと。`p0(W+1)` は `e0·w` を、`p0(W+W)` は `e1` を名指す | `Trans.BMS.OT_psi_Omega_add`, `Trans.BMS.val_tew`, `Trans.BMS.OT_te1` |

## 1 行: 行列が名指す順序数

| | |
|---|---|
| **展開が基本列であること** | `Trans.BMS.read_expandL` |
| **1 行の BMS が名指す順序数** | `Trans.BMS.bmsOrdEval` |
| それが `p0(W)` 未満であること（原始数列系の上限） | `Trans.BMS.read_lt_e0`, `Trans.BMS.bmsOrdEval_lt_e0` |
| かつ `p0(W)` 未満の標準形はすべてどれかが名指すこと | `Trans.BMS.exists_read`, `Trans.BMS.lt_e0_iff_allNil` |
| **かつ `e0` 未満の順序数はすべてどれかが名指すこと**。`p0(W)` は `e0` である | `Trans.BMS.exists_matrix_of_lt_eps0`, `Trans.BMS.val_te0` |
| だから 1 行が名指すのはその順序数ちょうどであること | `Trans.BMS.val_read_lt_eps0` |
| `val` が `e0` 未満の順序数の上へ全射であること | `Trans.BMS.exists_OT_of_lt_eps0` |
| **`e1` 未満へも全射であること**。`p0(W+W)` 未満の標準形が名指すのはちょうどそれ | `Trans.BMS.exists_OT_of_lt_eps1`, `Trans.BMS.exists_OT_lt_te1` |
| **だから `e1` 未満で `val` は全単射**。順序数一つに標準形一つ | `Trans.BMS.existsUnique_OT_lt_te1`, `Trans.BMS.existsUnique_OT_lt_te0` |
| **だから順序数の測度は `e0` への全単射であること** | `Trans.BMS.exists_bms_of_lt_eps0`, `Trans.BMS.bmsOrdEval_inj` |
| **系の階数がその順序数と一致すること**。二つの測度は一つである | `Trans.BMS.rank_prim_eq_val`, `Trans.BMS.rank_bms_eq_val` |
| **系そのものの順序数が `e0` であること**。階数はそこに共終で、決して届かない。成分列でも配列でも DBMS でも | `Trans.BMS.iSup_rank_prim`, `Trans.BMS.iSup_rank_bms`, `Trans.DBMS.iSup_rank_dbms` |
| 1 行の生成元が `w` の塔を名指すこと。`(0)` は `1`、`(0)(1)` は `w` | `Trans.BMS.val_twr_succ`, `Trans.BMS.rank_primGen` |
| 小さい行列は直接読める。`(0)(1)(1)` は `w^2`、`(0)(1)(2)` は `w^w`。対応表で二重に載っている項目はこれで決まる | `Trans.BMS.val_read_one_one`, `Trans.BMS.val_read_one_two` |
| **階数は順序数の測度のうち最小であること**。どの評価もそれを上から抑える | `Eval.rank_le` |
| DBMS の 1 行も同じ順序数を名指し、階数も一致すること | `Trans.DBMS.exists_dbms_of_lt_eps0`, `Trans.DBMS.rank_dbms_eq_val` |
| `p0(W)` 未満で項が基本列の上限であること | `Trans.BMS.fs_lub` |
| **標準 1 行行列とは、項が標準形である行列のことちょうどである** | `Trans.BMS.std_entries_iff`, `Trans.BMS.exists_bms_of_lt_e0` |
| **原始数列系と `p0(W)` 未満の標準形が同値であること** | `Trans.BMS.primEquivE0` |
| 1 行の行列は名指す順序数で決まり、自分の展開たちの上限であること | `Trans.BMS.bmsOrdEval_inj`, `Trans.BMS.expandL_lub` |
| ラベルではなく翻訳による 1 行の停止性 | `Trans.BMS.bms_one_terminates`, `Trans.BMS.prim_terminates` |
| 1 行 DBMS についての同じこと。こちらは他に停止性の証明がない | `Trans.DBMS.dbms_one_terminates`, `Trans.DBMS.dbmsOrdEval` |
| **行列の上の 1 行 DBMS**：状態は標準な配列の成分の列で、展開は `expandL` | `Trans.DBMS.dbmsL1`, `Trans.DBMS.dbmsL1Std`, `Trans.DBMS.dbmsL1_wf` |
| 成分を取る写像は、配列からこの系への全射で、括弧の番号も保つ。二つの配列が同じ状態に写るのは、同じ行列のときちょうどである。階数と順序数は変わらない | `Trans.DBMS.dbmsToL1`, `Trans.DBMS.dbmsToL1_map_eq_iff`, `Trans.DBMS.dbmsToL1_surjective`, `Trans.DBMS.rank_dbmsToL1`, `Trans.DBMS.dbmsOrdEval_val_eq` |
| **この系は原始数列の系そのもの**：列の上の恒等写像は単射かつ全射 | `Trans.DBMS.dbmsL1EquivPrim`, `Trans.DBMS.dbmsL1Prim_injective`, `Trans.DBMS.dbmsL1Prim_surjective` |
| **行列の上では順序数への写像は単射**で、`e0` 未満の順序数全部に全射、階数と一致し、順序を保つ | `Trans.DBMS.dbmsL1OrdEval_injective`, `Trans.DBMS.dbmsL1Ord_image`, `Trans.DBMS.rank_dbmsL1_eq_val`, `Trans.DBMS.dbmsL1OrdEval_lt_iff` |
| 配列 `dbms 1` の上では単射でない。理由は、配列が行列の外の値も持つことだけである。`(0)` と `(0)(1)[0]` は同じ行列である | `Trans.DBMS.dbmsOrdEval_not_injective`, `Trans.DBMS.dbmsHom_not_injective`, `Trans.DBMS.dbmsOrdEval_eq_iff` |

## 2 行以上: 階数がどこまで届くか

2 行の読み取りは無いので、これらが持つ順序数は展開関係の階数だけである。展開が
分かっている所なら、それでも計算できる。

| | |
|---|---|
| **2 行の生成元 `(0,0)(1,1)` の階数が `e0` であること**。2 行は 1 行が終わる所から始まる | `Trans.BMS.rank_pairGen` |
| どの行数でも、生成元は一つ少ない行の生成元たちの極限であること | `Trans.BMS.rank_gen_eq_iSup`, `Trans.BMS.rank_gen_lt` |
| `(0,0)` の階数が `1` で、末尾の 0 の列は 1 を足すこと。`(0,0)(1,1)(0,0)` は `e0 + 1` | `Trans.BMS.rank_zeroCol`, `Trans.BMS.rank_append_zeroCol`, `Trans.BMS.rank_succAll` |
| **展開がブロックを越えて戻らないこと**。行 `0` の成分が `0` の列がブロックの始まり | `Trans.BMS.expandRL_append` |
| **だから階数はブロックについて加法的**。ブロックの `n` 個並びは階数が `n` 倍 | `Trans.BMS.rank_appendState`, `Trans.BMS.rank_repNState` |
| **`m₀ = 0` なら展開は固定部分とブロックの繰り返し**。だから階数は `w` 倍になる | `Trans.BMS.expandRL_of_m0_zero`, `Trans.BMS.rank_mul_omega0` |
| よって `(0,0)(1,0)` は `w`、`(0,0)(1,1)(1,0)` は `e0·w`、`(0,0)(1,1)(0,0)(1,0)` は `e0 + w` | `Trans.BMS.rank_omegaCol`, `Trans.BMS.rank_omegaAll`, `Trans.BMS.rank_sumAll` |
| 繰り返せる。`(0,0)(1,1)(1,0)(1,0)` の階数は `e0·w^2` | `Trans.BMS.rank_omegaSqAll` |
| **その順序数にはどれも名前が付く**。上の階数は `p0(W)`・`p0(1)`・`p0(2)`・`p0(W+1)`・`p0(W+2)`・`e0+1`・`e0+w` の値である | `Trans.BMS.rank_genAll_val` とその隣の五つ |
| `rank_split_mul_omega0` は分割を直接受け取るので、この形の行列は 3 行で済む。`(0,0)(1,0)(1,0)` は `w^2`、`(0,0)(1,1)(0,0)(1,0)(1,0)` は `e0 + w^2` | `Trans.BMS.rank_split_mul_omega0`, `Trans.BMS.rank_omegaSqCol`, `Trans.BMS.rank_sumSqAll` |
| **族として**: `(0,0)(1,1)(1,0)^k` の階数は `e0·w^k` | `Trans.BMS.rank_MkState` |
| **だから 2 行の系の順序数は少なくとも `e0·w^w`**。粗い下界だが、読み取り無しで階数が与える | `Trans.BMS.eps0_mul_opow_omega0_le_iSup` |

届かないもの。`(0,0)(1,1)(2,1)` は `m₀ = 1` なので各コピーに加算が付いて互いに
違う。`(0,0)(1,1)(2,0)` は繰り返しではあるが、繰り返すのが `(1,1)` で、ブロックで
始まらない部分は自分の階数を持たない。それ以降の生成元も届かない。

`sorry` は無く、公理も `propext`・`Classical.choice`・`Quot.sound` の 3 つだけ。
`Googology.Core` で公理を使うのは、`Terminates` を結論する六つだけである。
`Rewrite.terminates_of_wf`、`Rewrite.terminates_of_measure`、`Eval.terminates`、
`Sim.terminates`、`Sim.terminates_transfer`、`Equiv.terminates_iff`。これらは
「無限に降下する列が無い」だけを仮定して「止まる状態がある」を要求する。そこが
古典的になる。`Core` の他のもの — 関係、整礎性、測度、四つの射 — はどれも公理を
一切使わない。

## 3 行：トリオ数列

| | |
|---|---|
| **`p0(W_a)` の trio 行列は標準形**（`a < e0`）。生成元から有限回の展開で届く 3 行の配列の成分である | `Trans.BMS.trioMatrix_std`, `Trans.BMS.omegaIndexMatrix_std`, `Trans.BMS.omegaIndexState` |
| **trio の写像は順序を保ち、順序を反映する**（`a < e0`、列の辞書式順序）。したがって単射 | `Trans.BMS.omegaIndexMatrix_lt_iff`, `Trans.BMS.omegaIndexMatrix_strictMono`, `Trans.BMS.omegaIndexMatrix_injective` |
| `e0 <= a < Λ` の規則 1〜10 の書き起こし。3 行で `z < 2` の形であること | `Trans.BMS.TrioRules.trioMatrixL`, `Trans.BMS.TrioRules.WF3_trioMatrixL` |
| **trio 数列の展開の共終性**。標準形の `b < a` には `b = a[k]` か `b < a[k]` となる `k` がある | `Trans.BMS.TrioCofinal.trio_cofinal`, `Trans.BMS.TrioCofinal.trioStd_cofinal` |
| koteitan/trio の展開と、この文庫の BMS の展開は、trio の標準形の上で同じ | `Trans.BMS.TrioCofinal.expandRL_toL`, `Trans.BMS.TrioCofinal.trioStdL_iff` |

## ペア数列 → 拡張ブーフホルツ ψ が展開を保たないこと

| | |
|---|---|
| **展開を保たず、展開と可換でもない**。生成元 `(0,0)(1,1)` を `[0]` で展開すると `(0,0)` で、`p0(W_1)` と `1` に写る。`p0(W_1)` の基本列の項は `1` にならない | `Trans.PSS.pairOrdTerm_step_ne_fs`, `Goals.pairToExb_not_preserves`, `Goals.pairToExb_not_commutes` |

## DBMS：`r` 行が `r + 1` 行の中に入ること

| | |
|---|---|
| **下に 0 の行を足す写像は標準形に入り、展開と可換で、単射で、階数を保つ** | `Trans.DBMS.exists_dstd_zeroRow`, `Trans.DBMS.dbmsL_homSucc`, `Trans.DBMS.dbmsL_homSucc_injective`, `Trans.DBMS.rank_dbmsL_homSucc` |
| 全射ではない。生成元 `(0,0)(1,0)(2,1)` は像に無い | `Trans.DBMS.dbmsToSucc_not_surjective` |
| `r ≤ s` なら `r` 行は `s` 行を模倣する | `Trans.DBMS.dbmsL_simAdd`, `Trans.DBMS.dbmsL_simLe` |

## 3 行：共終性を ψ の項で

| | |
|---|---|
| **極限の `a < e0` で、`p0(W_a)` の基本列と、その trio 行列の展開は互いに共終** | `Trans.BMS.TrioCofPsi.trioPsi_fs`, `Trans.BMS.TrioCofPsi.trioPsi_expand_prefix` |
| `p0(W_b) < p0(W_a)` なら `M(b) ≤ M(a)[k]` となる `k` がある | `Trans.BMS.TrioCofPsi.trioPsi_cofinal`, `Trans.BMS.TrioCofPsi.trioPsi_cofinal_val` |

## 3 行：規則 1〜10 と `trioMatrix`、BMS の全射性

| | |
|---|---|
| **規則 1〜10 の書き起こしは `e0` 未満で `trioMatrix` と一致する**（深さ 201 以下） | `Trans.BMS.TrioRulesE0.trioMatrixL_eq_trioMatrix'`, `Trans.BMS.TrioRulesE0.predBetaSpec` |
| BMS の `r` 行 → `r + 1` 行は全射でない | `Trans.BMS.bmsToSucc_not_surjective` |

## 2 行の DBMS と、ペア数列 → ψ の到達

| | |
|---|---|
| **2 行の DBMS の順序数への翻訳写像**。単射、`p0(W_w)` 未満への全射、階数と一致、順序を保つ | `Trans.DBMS.dbmsL2OrdEval`, `Trans.DBMS.dbmsL2OrdEval_injective`, `Trans.DBMS.dbmsL2Ord_image`, `Trans.DBMS.rank_dbmsL2_eq`, `Trans.DBMS.ltPS_iff_dOrdL_lt` |
| 2 行の DBMS の標準形はブロックの並び | `Trans.DBMS.dreach2_iff_dform`, `Trans.DBMS.expand2L_blk_some`, `Trans.DBMS.expand2L_blk_none` |
| **ペア数列の 1 手は ψ の側の 1 手以上に写る**。到達は両方向に保たれる | `Trans.PSS.pairToExbOT_transGen_iff`, `Goals.pairToExb_transGen_iff` |
| **ψ の手数に上限は無い**。`(0,0)...(p,p)(p+1,p)[0]` はちょうど `p+1` 手 | `Goals.pairToExb_steps_unbounded`, `Goals.pairToExb_min_steps`, `Trans.PSS.StepBound.lastSub_fs_idx` |

## 3 行：後続での共終性と、燃料

| | |
|---|---|
| **後続の `a = b + 1 < e0` で、`p0(W_a)` の基本列と `M(a)` の展開は互いに共終** | `Trans.BMS.TrioSucc.trioPsi_fs_succ`, `Trans.BMS.TrioSucc.fs_psiOmega_succ` |
| **燃料を深さで与えた規則 1〜10 は、すべての `a < e0` で `trioMatrix` と一致** | `Trans.BMS.TrioFuel.trioMatrixD_eq_trioMatrix`, `Trans.BMS.TrioFuel.trioMatrixF_200` |

## DBMS：何行でもブロック分解、3 行の最初の生成元

| | |
|---|---|
| **何行でも、DBMS の階数は `w^rank(M_0) + ... + w^rank(M_k)`** | `Trans.DBMS.rank_dbmsL_eq_sum`, `Trans.DBMS.rkL_blkR`, `Trans.DBMS.rkL_append` |
| **3 行の生成元 `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` の階数は `p0(W_w)`** | `Trans.DBMS.rank_gen_three_three`, `Trans.DBMS.rkL_cgen_three`, `Trans.DBMS.rank_gen_top` |
| 中身の系の生成元は BMS の生成元を持ち上げたもの。3 行の DBMS の生成元 `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` と BMS の `(0,0,0)(1,1,1)` は同じ階数 | `Trans.DBMS.cgen_two_eq_lift`, `Trans.DBMS.expandRL_lift`, `Trans.DBMS.rank_genL_two_three_eq_bms` |

## 3 行：添字が 0 か 1 だけの項

| | |
|---|---|
| **添字が 0 か 1 だけの可算な標準形の項で、構造的な写像 `trioE` は標準形を出し、順序を保ち、順序を反映する** | `Trans.BMS.TrioTreeStd.trioE_std`, `Trans.BMS.TrioTree.trioE_lt_iff`, `Trans.BMS.TrioTree.trioE_injective` |
| 深さ 200 以下では規則 1〜10 は `trioE` と一致し、標準形を出し、順序を保つ | `Trans.BMS.TrioTreeRules.trioMatrixL_eq_trioE`, `Trans.BMS.TrioTreeRules.trioMatrixL_std`, `Trans.BMS.TrioTreeRules.trioMatrixL_lt_iff` |
