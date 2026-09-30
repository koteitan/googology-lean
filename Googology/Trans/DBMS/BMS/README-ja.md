[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/DBMS/BMS

DBMS → BMS。成分列の上の 1 行、ブロックとその標準形の並び、3 行 DBMS と 3 行 BMS の比較（`ThreeRow*`）。

## ファイル

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| DBMS、BMS（原始数列） | `OneRowL.lean` | `StepHom`、`Equiv` | **行列の上の 1 行の DBMS**（`dbmsL1`）。配列は成分によってこの系の上へ写る。この系は原始数列の系そのものである。その順序数への写像は単射で、`e0` 未満の順序数全部に全射、階数と一致し、順序を保つ |
| DBMS どうし | `Blocks.lean`、`ThreeRow.lean` | `StepHom`、階数 | **何行でも、DBMS の標準形はブロックの並びで、階数は `w^rank(M_0) + ... + w^rank(M_k)`**（`rank_dbmsL_eq_sum`）。各 `M_i` は生成元 `(0,0,0)(1,1,0)(2,2,1)...` から届く「中身の系」の元。3 行では `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` の階数が `p0(W_w)`（`rank_gen_three_three`）。その先の生成元の階数は未解決 |
| DBMS、BMS | `ContentLift.lean`、`ThreeRowLift.lean` | — | **中身の系 `C_3` の生成元は、BMS の生成元を持ち上げたもの**（`cgen_two_eq_lift`）。持ち上げは展開と可換（`expandRL_lift`）。3 行の DBMS の生成元 `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` と BMS の `(0,0,0)(1,1,1)` は同じ階数（`rank_genL_two_three_eq_bms`）。一般の場合（3 行の DBMS と BMS は同じ順序数）は予想 |
| DBMS、BMS | `ThreeRowLower.lean` | — | **3 行の BMS ≤ 3 行の DBMS**。持ち上げで階数は下がらない（`rkL_le_rkL_lift`）ので、すべての n で `rkL 2 (bgen3 n) ≤ rkL 2 (cgen 2 (n+2))`。3 行の BMS の順序数は 3 行の DBMS の順序数以下（`iSup_rank_bmsL_two_le_dbmsL`）。逆向きは n ≥ 2 で未解決 |
| DBMS、BMS | `ThreeRowUpper.lean`、`ThreeRowUpperRefute.lean`、`ThreeRowUpperComm.lean` | — | **n = 2 で 3 行の DBMS ≤ BMS に向けて**。写像 `t3`（列 1 の `(1,1,0)` を `(1,1,1)` にする）は展開で辞書式に下がる（`t3_expand_lt`）。可換でない 2 つの場合に `t3` で階数が下がれば（`T3RankDescNC`、未解決）、`rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)`（`rkL_cgen_two_four_eq_of_NC`）。「`t3 C` はトリオの標準形」は偽（`not_t3Std`） |
| DBMS、BMS | `../DBMS/ThreeRowUpperNC*.lean`、`../DBMS/ThreeRowUpperRP*.lean`、`ThreeRowUpperPushBMS.lean` | — | **n = 2 をトリオ数列の 1 つの命題に帰着**。入れ子の持ち上げ `t3n` で、可換でない場合を上げられる親の位置で分けた。最後から 2 つ目の列の場合と `RPLastShape` は証明済み。`rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)` は `T3nPushStd`（未解決：`t3n C` がトリオの標準形なら `t3n (pushL C y)` もそう。約 160 万の行列で失敗 0）から出る（`rkL_cgen_two_four_eq_of_push`）。`T3nPushStd` はさらに、トリオの行列だけの命題 `TrioPushStd` に帰着した：トリオの標準形 `S` の最後の列が行 2 の親 `x` を持ち、`y > x` がその行 1 の祖先なら、写し `pushS S y` もトリオの標準形（48,438 例で失敗 0。`y = x` では偽）（`rkL_cgen_two_four_eq_of_trioPush`） |
| DBMS どうし | `BlocksStd.lean` | — | **標準形のブロックの並びの条件**（何行でも）。標準形なら、中身は前から順に届き合い、階数は減っていく（`dchain_of_dstdL`、`drank_of_dstdL`）。ブロック 1 つは常に標準形（`dstdL_blkR`）。逆向きは、階数の単射性 `RkInj` か、最後のブロックを複製できること `DupProp` から出る（`dstdL_iff_drank_of_inj`、`dstdL_iff_dchain_of_dup`） |
| DBMS どうし | `BlocksSuff.lean` | — | **標準形のブロックの並びの特徴づけ**（何行でも）。ブロックの並びが標準形であることと、中身が前から順に届き合うことは同値（`dstdL_iff_dchain`）。最後のブロックはいつでも複製できる（`dupProp`） |
| DBMS どうし | `BlocksLex.lean` | — | **「届く」と辞書式の順序**（何行でも）。1 回の展開で列の並びは辞書式に小さくなる（`expandRL_lt_self`）ので、届けば `≤`。「標準形 ⟺ 中身が辞書式に増えない」は `LexReach r` と同値（`lexReach_iff_dstdL_iff_dlex`）。 |
| DBMS どうし | `LexReachThree.lean` | — | **標準形 ⟺ 中身が辞書式に増えない**（何行でも `dstdL_iff_dlex`、3 行は `dstdL_three_iff_dlex`）。`M[N+1]` は `M[N]` に届き、生成元どうしも届き合うので、中身の上で「届く」は全順序（`reachTotal`）。よって `LexReach r` はすべての `r` で成り立つ |
