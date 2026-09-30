[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/BMS/common

複数の翻訳が使う、BMS だけについての事実。成分列の上の展開（行数によらない）、0 の行、切り取りと継ぎ足し、3 行の展開の共終性（`TrioCof/`）。

## ファイル

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| BMS 自身 | `OneRow.lean` | — | 1 行の展開が原始数列の規則であること: 最初の `p` 個を残し、続く `s` 個を `N + 1` 回繰り返す |
| BMS 自身 | `Rows.lean` | — | 親を名指せば bad root が決まること。行数によらない |
| BMS 自身 | `Entries.lean` | — | 配列とその成分列が同じ展開をすること |
| BMS 自身 | `TwoRow.lean` | — | 2 行の展開: `m₀` は 0 か 1 で、1 のとき行 0 に加算が入る |
| BMS 自身 | `Anc.lean` | — | 行 0 の祖先関係を成分列から読み、計算できる形にして `BM4.anc` と一致することを示す |
| BMS 自身 | `EntriesR.lean` | — | **BMS の展開を行数によらず成分列の上に書き、それが `BM4.expand` であること** — だから走る |
| BMS 自身 | `AllL.lean` | `Sim` | 標準形かどうかによらず**全**行列上の規則を、走る系として与え、標準形はその中に置く |
| BMS 自身 | `Zero.lean` | — | 下に 0 の行を足しても何も変わらないこと。2 行の規則がそこでは 1 行の規則になる |
| BMS 自身 | `Embed.lean` | `StepHom` | **原始数列系がペア数列系の中に入ること** |
| BMS 自身 | `ZeroRow.lean` | `StepHom`, `Sim` | **それが行数によらず成り立つこと**。`r + 1` 行が `r + 2` 行の中に、`s ≥ r` なら `s + 1` 行の中に入る |
| BMS どうし | `ZeroRowSurj.lean` | — | BMS の `r` 行 → `r + 1` 行は全射でない。生成元 `(0,0)(1,1)` は像に無い（`bmsToSucc_not_surjective`） |
| BMS 自身 | `Append.lean` | — | **展開が最後のブロックしか見ないこと**。行 `0` の成分が `0` の列がブロックの始まりで、親はそこを越えて戻らない |
| BMS 自身 | `Entries2.lean` | — | **2 行の展開を成分列の上に書き、それが `BM4.expand` であること、そして走らせれば止まること** |
| BMS 自身 | `Pair.lean` | — | ペア数列系を、ステップが走る `Rewrite` として与え、生成元も付ける |
| BMS 自身 | `Agree.lean` | — | 1 行・2 行・一般の規則が一致すること。一般の系も生成元付きの `Rewrite` にする |
| BMS 自身 | `Same.lean` | `Equiv` | 一般の系の 1 行が原始数列系**そのもの**、2 行がペア数列系そのものであること |
| BMS 自身 | `Cut.lean` | — | ブロック再帰 `expandL` が教科書どおりの規則であること: 最後の列を落とし、悪い部分を `N + 1` 回繰り返す |
| 3 行の BMS | `TrioCof/`、`TrioCofinal.lean` | [koteitan/trio](https://github.com/koteitan/trio) | **trio 数列の展開の共終性**。koteitan/trio の `trio_cofinality` とその依存 16 ファイルを移し、この文庫の BMS の展開と同じであることを証明した（`expandRL_toL`）。標準形の `b < a` には、`b ≤ a[k]` となる `k` がある（`trio_cofinal`、`trioStd_cofinal`） |
