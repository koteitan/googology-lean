[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans/BMS/ExBuchholz

BMS → 拡張ブーフホルツ ψ。行列がどの順序数を名指すか。1 行（ε₀ 未満、ε 数、ζ₀、階数 = 値）と、ペア数列（階数 = 1 + val、`PSS/`）。

- [PSS/](PSS/README-ja.md): 2 行（ペア数列）。
- 逆向きの、拡張ブーフホルツ ψ → トリオ数列は [../../ExBuchholz/BMS/](../../ExBuchholz/BMS/README-ja.md) にある。

## ファイル

| 対 | ファイル | 構造 | 状態 |
|---|---|---|---|
| BMS、拡張ブーフホルツ ψ | `Calibrate.lean` | — | `p0(W)` 未満が添字全部 0 とちょうど一致すること。よって読み取りはそこの標準形を全部拾う |
| BMS、拡張ブーフホルツ ψ | `Eps0.lean` | — | **1 行が名指すのは `e0` 未満の順序数ちょうどであること**。そこで `val` は全射で、証明は Cantor 標準形。`p0(W)` は `e0` である。同じ構成を `e1` まで伸ばしてある。先頭項が `p0(W + B)` になる |
| BMS、拡張ブーフホルツ ψ | `EpsN.lean` | — | **`val` が全ての `e_n` 未満へ、したがって `e_w` 未満へ全射であること**。`n` についての帰納法で、段は `e1` の構成そのものである。`W·n + B` を項にして、先頭項を `p0(W·(n+1) + B)` にする。極限が `p0(p1(1))` である |
| BMS、拡張ブーフホルツ ψ | `Arg.lean`, `EpsBig.lean` | — | **`val` が `e_{e0}` 未満へ全射であること**。そこでは全単射である。`mu < e0` の全てで `W·mu` を名指す項を Cantor 標準形から作り（`W·w^e` は `p1(e)`）、その上で同じ先頭項の構成を `d < e0` の全段で回す |
| BMS、拡張ブーフホルツ ψ | `Zeta.lean` | — | **`val` が `z0` 未満へ全射であること**。しかも標準形はただ一つである。引数の項と値の項を一本の帰納法で作るので、指数自身が e 数でも、その添字が与える段で名指される。`C_0(Λ)` への全射という一般の形は `Notation.ExBuchholz.Term.Vals_eq` である。これらのファイルはどの項がどの順序数を名指すかを言い、一般の定理はそれを言わない |
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
