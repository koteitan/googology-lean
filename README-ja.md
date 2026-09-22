[English](README.md) | [Japanese](README-ja.md)

# googology-lean

巨大数のための Lean 4 ライブラリ。展開系、順序数表記系、その間の翻訳を扱う。

巨大数の系——BMS、DBMS、Y 数列——について問われるのは、どの展開列も有限で止まるか
どうかである。このライブラリはその問いに一度だけ答え、個別の系はその系に固有のもの
だけを出せばよいようにしてある。

## 何が証明されているか

名前は `Googology` からの相対で書く。

### 系

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
| 成分列の上の系と、その生成元 | `Trans.BMS.prim`, `Trans.BMS.pairL`, `Trans.BMS.bmsL` |
| 一般の系の 1 行が原始数列系、2 行がペア数列系であること | `Trans.BMS.bmsEquivPrim`, `Trans.BMS.pairEquivBms` |
| 生成元から出発した展開列は必ず止まること | `Notation.BMS.bmsStd_terminates`, `Notation.DBMS.dbmsStd_terminates`, `Trans.BMS.bmsLStd_terminates` |
| **整礎性と停止性は同じ条件であること** | `Rewrite.wf_iff_terminates` |
| だからここにある系はどれも整礎で、展開が階数を持つこと | `Trans.BMS.bmsL_wf`, `Trans.BMS.pairL_wf`, `Trans.BMS.prim_wf`, `Trans.BMS.bmsLRankEval` |
| DBMS は同じ規則で生成元だけが違い、やはり停止する | `Notation.DBMS.dbms_terminates`, `Trans.DBMS.dbmsL_terminates` |

### 拡張ブーフホルツ ψ

| | |
|---|---|
| **標準形は整列する** | `Notation.ExBuchholz.Term.OTLt_wf` |
| 異なる標準形は異なる順序数を名指す | `Notation.ExBuchholz.Term.val_inj_of_OT` |
| 表記系の正しさ。項の順序と順序数の順序が一致する | `Notation.ExBuchholz.Term.val_lt_val` |
| 基本列が降下する | `Notation.ExBuchholz.Term.fs_lt` |
| **拡張ブーフホルツ項は停止する** | `Notation.ExBuchholz.Term.exbOT_terminates` |
| 基本列が標準形を保つ（Buchholz 補題 3.3） | `Notation.ExBuchholz.Term.OTFS_thm` |
| **`e0` 未満で `p0(a) = w^a` であること**。`p0(a) <= w^a` は常に成り立つ | `Notation.ExBuchholz.Ord.psi_zero_eq_opow`, `Notation.ExBuchholz.Ord.psi_zero_le_opow` |
| **`p0(W) = e0`** | `Notation.ExBuchholz.Ord.psi_Omega_one` |

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
| **だから順序数の測度は `e0` への全単射であること** | `Trans.BMS.exists_bms_of_lt_eps0`, `Trans.BMS.bmsOrdEval_inj` |
| **系の階数がその順序数と一致すること**。二つの測度は一つである | `Trans.BMS.rank_prim_eq_val`, `Trans.BMS.rank_bms_eq_val` |
| DBMS の 1 行も同じ順序数を名指し、階数も一致すること | `Trans.DBMS.exists_dbms_of_lt_eps0`, `Trans.DBMS.rank_dbms_eq_val` |
| **2 行の生成元 `(0,0)(1,1)` の階数が `e0` であること**。2 行は 1 行が終わる所から始まる | `Trans.BMS.rank_pairGen` |
| どの行数でも、生成元は一つ少ない行の生成元たちの極限であること | `Trans.BMS.rank_gen_eq_iSup`, `Trans.BMS.rank_gen_lt` |
| `(0,0)(1,1)(0,0)` の階数が `e0 + 1` であること。最後の列に親が無いのでどの括弧でも落ちる | `Trans.BMS.rank_succAll`, `Rewrite.rank_succ_of_const_step` |
| **展開がブロックを越えて戻らないこと**。行 `0` の成分が `0` の列がブロックの始まり | `Trans.BMS.expandRL_append` |
| **だから階数はブロックについて加法的**。`(0,0)(1,1)` の `n` 個並びの階数は `e0·n` | `Trans.BMS.rank_appendState`, `Trans.BMS.rank_blockRepState` |
| `(0,0)(1,1)(1,0)` の階数が `e0·w` であること | `Trans.BMS.rank_omegaAll` |
| `p0(W)` 未満で項が基本列の上限であること | `Trans.BMS.fs_lub` |
| **標準 1 行行列とは、項が標準形である行列のことちょうどである** | `Trans.BMS.std_entries_iff`, `Trans.BMS.exists_bms_of_lt_e0` |
| **原始数列系と `p0(W)` 未満の標準形が同値であること** | `Trans.BMS.primEquivE0` |
| 1 行の行列は名指す順序数で決まり、自分の展開たちの上限であること | `Trans.BMS.bmsOrdEval_inj`, `Trans.BMS.expandL_lub` |
| ラベルではなく翻訳による 1 行の停止性 | `Trans.BMS.bms_one_terminates`, `Trans.BMS.prim_terminates` |
| 1 行 DBMS についての同じこと。こちらは他に停止性の証明がない | `Trans.DBMS.dbms_one_terminates`, `Trans.DBMS.dbmsOrdEval` |

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

## ライセンス

MIT ライセンス。[LICENSE](LICENSE) を参照。

---

## 開発する人へ

* [spec-ja.md](spec-ja.md) — ライブラリの構成と書き方の規約。この文書群をどう書くかの
  規則も含む
* [plan-ja.md](plan-ja.md) — 議論の全体と、作業の現在地

現状：`Core/` は完成。`Notation/ExBuchholz` は表記系としても展開系としても完成
した。停止性は何も仮定せずに証明してある。`Notation/BMS` はどの行数でも停止する。
`Trans/` には最初の項目が入った。1 行の Bashicu 行列を拡張ブーフホルツ項として
読む写像である。何が足りないかは `plan-ja.md` にある。
