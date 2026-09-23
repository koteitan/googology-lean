[English](README.md) | [Japanese](README-ja.md)

# googology-lean

巨大数のための Lean 4 ライブラリ。展開系、順序数表記系、その間の翻訳を扱う。

巨大数の系——BMS、DBMS、Y 数列——について問われるのは、どの展開列も有限で止まるか
どうかである。このライブラリはその問いに一度だけ答え、個別の系はその系に固有のもの
だけを出せばよいようにしてある。

## 何が証明されているか

名前は `Googology` からの相対で書く。

### 系

| 表記 | 展開の定義 | 停止性・整礎性 | 標準形でない配列からも停止 | 順序数の測度（階数） | 下の段の系を含む | 名指す順序数 | 系全体の順序数 |
|---|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| 原始数列（BMS 1 行） | ✅ | ✅ | ✅ | ✅ |  | ✅ | ✅ |
| ペア数列（BMS 2 行） | ✅ | ✅ | ✅ | ✅ | ✅ |  |  |
| トリオ数列（BMS 3 行） | ✅ | ✅ | ✅ | ✅ | ✅ |  |  |
| BMS（任意の行数） | ✅ | ✅ | ✅ | ✅ | ✅ |  |  |
| DBMS（1 行） | ✅ | ✅ | ✅ | ✅ |  | ✅ | ✅ |
| DBMS（任意の行数） | ✅ | ✅ | ✅ | ✅ |  |  |  |
| Y 数列（1-Y） | ✅ |  |  |  |  |  |  |
| 拡張ブーフホルツ ψ | ✅ | ✅ |  | ✅ |  | ✅ | ✅ |

- 展開の定義：展開を Lean の関数として書き、実際に計算できる。BMS は `BM4.expand` と一致することまで証明してある。Y 数列は公式プログラムの書き起こしで、公式実装の出力と 213 件で照合した。
- 停止性・整礎性：どの展開列も有限で止まる。整礎性と停止性が同じ条件であることも証明してある。
- 下の段の系を含む：下に 0 の行を足すと、1 行少ない系がそのまま入る。
- 名指す順序数：状態ごとに順序数を与える。原始数列と DBMS 1 行では、それが展開の階数と一致し、`e0` 未満の順序数ちょうどになる。拡張ブーフホルツ ψ では標準形の値で、標準形から `C_0(Λ)` への順序同型になる（階数との一致は未証明）。
- 系全体の順序数：原始数列と DBMS 1 行は `e0`、拡張ブーフホルツ ψ の可算な標準形は `p0(Λ)` である。
- Y 数列の停止性はこのライブラリの外で証明されていて、引用にとどめている（`Googology/Notation/Y/README-ja.md`）。

### 拡張ブーフホルツ ψ

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

### 1 行: 行列が名指す順序数

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

### 2 行以上: 階数がどこまで届くか

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

## 使い方

`lakefile.toml` に足す。

```toml
[[require]]
name = "googology"
git = "https://github.com/koteitan/googology-lean"
```

たとえば次のように使える。

```lean
import Googology

open Googology Notation.BMS

-- 5 行のバシク行列は停止する。
example : (bms 5).Terminates := bms_terminates 5
```

## 考え方

展開系は状態の型そのものをフィールドに持つ。だから型の違う系が 1 つの命題を共有
できる。

```lean
structure Rewrite where
  State  : Type
  step   : State → Nat → State
  halted : State → Prop
```

型クラスではなく構造体にしてあるのは意図的である。1 つの状態型に複数の展開規則が
乗るため（BMS の BM4 / 3.3 / 2 / 1.1）で、状態型を鍵にした型クラスでは 1 つしか
持てない。

### 一度だけ証明して、全系が使うもの

| 名前 | 主張 |
|---|---|
| `Rewrite.terminates_of_wf` | 整礎性 ⟹ 停止性 |
| `Rewrite.wf_of_measure` | 任意の整礎順序への測度 ⟹ 整礎性 |
| `Rewrite.terminates_of_measure` | 測度 ⟹ 停止性 |
| `Rewrite.Std.of_terminates` | 全状態の停止性 ⟹ 標準形の停止性 |
| `OrdHom.wf` | 狭義単調な写像で整礎性が移る |
| `OrdHom.injective` | 三分律＋非反射律 ⟹ 単射 |
| `Sim.wf`、`Sim.terminates` | 模倣で整礎性と停止性が移る |
| `Sim.terminates_transfer` | 停止性が模倣に沿って手前に移る |
| `StepHom.toSim` | 展開と可換なら模倣になる |
| `Equiv.wf_iff`、`Equiv.terminates_iff` | 互いに逆な翻訳があれば両者は同値 |
| `Eval.terminates` | 整礎順序への評価 ⟹ 停止性 |
| `Eval.compOrd` | 評価 ∘ 順序を保つ写像 = 評価 |
| `Eval.ofSim` | 模倣で評価を手前に引き戻せる |
| `Rewrite.rankEval` | 整礎な系は自前の順序数の測度を持つ |

最後の 3 つが背骨である。翻訳と行き先の評価を合わせると、元の系の停止性が 1 行で
出る。

```lean
example (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO
```

## 系を足すには

`Rewrite` の 3 つのフィールドを与え、停止性を証明したいなら測度を 1 つ出す。測度の
行き先は、整礎関係の入った型なら何でもよい（`Nat`、順序数、自作の項）。一歩ごとに
狭義に下がることを言えば、残りは定理として受け取れる。

すでに別のところで停止性が証明されている系なら、数行で繋がる。`Notation/BMS` が
その実例。

## 中身

```
Googology/
  Core/            展開系、標準形、翻訳
  Rank.lean        整礎な系は順序数の測度を持つ
  Notation/        系そのもの
    BMS/             バシク行列。行数は任意
    ExBuchholz/      拡張ブーフホルツ ψ
    DBMS/            生成元の違う BMS
    Y/               Y 数列
  Trans/           2 つの系の間の翻訳
```

各ディレクトリに README がある。

## ビルド

```sh
lake build
```

Lean 4 v4.30.0。依存は 2 つで、mathlib と、BMS の停止性証明のための
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern)。
`Googology.Core` はどちらも import しないので、停止性の道具一式は mathlib 無しで
読めて使える。

## 出典

このライブラリが使っている他者の成果と、使っている場所。koteitan のリポジトリは
使う場所でリンクしてあり、ここには挙げない。

| 出典 | 何を取ったか | 場所 |
|---|---|---|
| [mathlib](https://github.com/leanprover-community/mathlib4)（Apache-2.0） | 順序数、基数、その土台 | 依存。`Core` の外で import する |
| BashicuHyudora、[BASIC言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81) | バシク行列システムとその版 BM4 | `Notation/BMS/`。規則の実装は依存先の koteitan/bms-elem-pattern にある |
| Maksudov の拡張ブーフホルツ ψ。[Googology Wiki](https://googology.miraheze.org/wiki/Extended_Buchholz%27s_function) の記述 | `ψ_v(a)` と `C_v(a)` の定義 | `Notation/ExBuchholz/Ord.lean` |
| p進大好きbot、[拡張Buchholz OCFに伴う順序数表記](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E6%8B%A1%E5%BC%B5Buchholz_OCF%E3%81%AB%E4%BC%B4%E3%81%86%E9%A0%86%E5%BA%8F%E6%95%B0%E8%A1%A8%E8%A8%98) | 項、その順序、`G`、`OT`、評価、`dom` と `[ ]`、`val` が `C_0(Λ)` への同型だという主張 | `Notation/ExBuchholz/` |
| W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic 32 (1986) 195–207 | 基本列が依って立つ補題 3.2–3.6 | `Notation/ExBuchholz/FS.lean`、`Closure.lean` |
| Yukito 氏の Y 数列と、その公式プログラムである Naruyoko/YNySequence の [`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js)（revision `2de1397`） | 文ごとに書き起こした定義。検算の期待値 | `Notation/Y/Yukito.lean`、`test/YCheck.lean` |
| [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)（Apache-2.0） | 1-Y の停止性の引用のみ。複製も翻案もしていない | `Notation/Y/README.md` |
| wiki の記事 [ペア数列数](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0) と [Y数列](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97) | 背景と対応表 | `plan.md` |

`Notation/Y/Yukito.lean` の書き起こしは `script.js` を Lean に訳したものである。
`Naruyoko/YNySequence` にはライセンスのファイルが無い。

## ライセンス

MIT ライセンス。[LICENSE](LICENSE) を参照。

---

## 開発する人へ

* [spec-ja.md](spec-ja.md) — ライブラリの構成と書き方の規約。この文書群をどう書くかの
  規則も含む
* [plan-ja.md](plan-ja.md) — 議論の全体と、作業の現在地

現状：`Core/` は完成。`Notation/ExBuchholz` は表記系としても展開系としても完成
した。停止性は何も仮定せずに証明してある。`Notation/BMS` はどの行数でも停止する。
`Trans/` は 1 行を完全に決着させた。項としても、順序数としても、系の階数としても
一致する。2 行の読み取りは無いままだが、2 行の順序数もいくつか出ている。何が
足りないかは `plan-ja.md` にある。
