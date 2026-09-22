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
| 原始数列・ペア数列・トリオ数列の停止 | `Notation.BMS.primitive_terminates`、`Notation.BMS.pair_terminates`、`Notation.BMS.trio_terminates` |
| BMS は順序数の測度を持つ | `Notation.BMS.bmsEval` |
| **成分列の上に書いた BMS の展開が `BM4.expand` であること** — 行数によらず、だから走る | `Trans.BMS.entriesR_expand` |
| 1 行・2 行・一般の規則が一つの規則であること | `Trans.BMS.expandRL_one`, `Trans.BMS.expandRL_two` |
| 成分列の上の系と、その生成元 | `Trans.BMS.prim`, `Trans.BMS.pairL`, `Trans.BMS.bmsL` |
| DBMS は同じ規則で生成元だけが違う | `Trans.DBMS.dbmsL`, `Trans.DBMS.dbmsL_zero_terminates` |

### 拡張ブーフホルツ ψ

| | |
|---|---|
| **標準形は整列する** | `Notation.ExBuchholz.Term.OTLt_wf` |
| 異なる標準形は異なる順序数を名指す | `Notation.ExBuchholz.Term.val_inj_of_OT` |
| 表記系の正しさ。項の順序と順序数の順序が一致する | `Notation.ExBuchholz.Term.val_lt_val` |
| 基本列が降下する | `Notation.ExBuchholz.Term.fs_lt` |
| **拡張ブーフホルツ項は停止する** | `Notation.ExBuchholz.Term.exbOT_terminates` |
| 基本列が標準形を保つ（Buchholz 補題 3.3） | `Notation.ExBuchholz.Term.OTFS_thm` |

### 1 行: 行列が名指す順序数

| | |
|---|---|
| **展開が基本列であること** | `Trans.BMS.read_expandL` |
| **1 行の BMS が名指す順序数** | `Trans.BMS.bmsOrdEval` |
| それが `p0(W)` 未満であること（原始数列系の上限） | `Trans.BMS.read_lt_e0`, `Trans.BMS.bmsOrdEval_lt_e0` |
| かつ `p0(W)` 未満の標準形はすべてどれかが名指すこと | `Trans.BMS.exists_read`, `Trans.BMS.lt_e0_iff_allNil` |
| `p0(W)` 未満で項が基本列の上限であること | `Trans.BMS.fs_lub` |
| **標準 1 行行列とは、項が標準形である行列のことちょうどである** | `Trans.BMS.std_entries_iff`, `Trans.BMS.exists_bms_of_lt_e0` |
| **原始数列系と `p0(W)` 未満の標準形が同値であること** | `Trans.BMS.primEquivE0` |
| ラベルではなく翻訳による 1 行の停止性 | `Trans.BMS.bms_one_terminates`, `Trans.BMS.prim_terminates` |
| 1 行 DBMS についての同じこと。こちらは他に停止性の証明がない | `Trans.DBMS.dbms_one_terminates`, `Trans.DBMS.dbmsOrdEval` |

`sorry` は無く、公理も `propext`・`Classical.choice`・`Quot.sound` の 3 つだけ。
`Googology.Core` はそのどれも使わない。

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
