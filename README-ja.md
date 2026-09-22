[English](README.md) | [Japanese](README-ja.md)

# googology-lean

巨大数のための Lean 4 ライブラリ。展開系、順序数表記系、その間の翻訳を扱います。

共通の定理を**一度だけ**証明しておき、個別の系はその系に固有のもの——たいていは
測度 1 つ——だけを出せばよいようにします。

## どこから読むか

| | |
|---|---|
| [plan-ja.md](plan-ja.md) | 議論の全体と、作業の現在地 |

## ディレクトリ構造

```
Googology/
  Core/            系に依存しない中核。core Lean 以外に依存しない
    Rewrite.lean     展開系、Rel、WF、Terminates
    Std.lean         標準形と生成元
    Morphism.lean    OrdHom、Sim、StepHom、Equiv、Eval
  Rank.lean        整礎な系は順序数の測度を持つ
  Notation/        表記系。互いに import しない
    BMS/             バシク行列。行数は任意
    ExBuchholz/      拡張ブーフホルツ psi
    DBMS/  Y/  …     まだ無い
  Trans/           具体的な翻訳。2 つの系を import する唯一の層
    BMS/
      DBMS.lean
      Y.lean
      OTB.lean
test/              骨組みの確認。架空の規則で、実在の系ではない
```

### 層の規則

1. `Core/` は core Lean 以外に依存しません。mathlib 非依存のプロジェクトから使える
2. `Notation/X/` は `Notation/Y/` を import しません。系は自分のことしか知らない
3. `Trans/` だけが 2 つの系を同時に import する
4. 対 `{X, Y}` には**ファイルを 1 つ**だけ置きます。名前順で先に来る方の下に置き、
   両方向と、あれば `Equiv` をまとめて入れる。どちら側からでも引けるように、
   [Trans/README-ja.md](Googology/Trans/README-ja.md) に索引を置く

規則 2 が import の向きを保ちます。翻訳を `Notation/BMS/Trans/DBMS.lean` に置くと、
BMS を import しただけで DBMS が付いてきて、最後には全部の系が付いてきます。

巨大数の側で定義された系と、証明論の文献から来た系は、同じ種類のものである
——項の型、順序、基本列——から、1 つのディレクトリに同居させます。mathlib は
系ごとに import します。順序数へ評価する系だけが import します。

## 中核

展開系は状態の型そのものをフィールドに持ちます。だから型の違う系が 1 つの型に収まり、
同じ命題を共有できます。

```lean
structure Rewrite where
  State  : Type
  step   : State → Nat → State
  halted : State → Prop
```

型クラスにしていないのは意図的です。1 つの状態型に複数の展開規則が乗るため
（BMS の BM4 / 3.3 / 2 / 1.1）で、状態型を鍵にした型クラスは 1 つしか持てません。

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
| `Rewrite.rankEval` | 整礎な系は自前の順序数の測度を持つ（mathlib が要る） |

最後の 2 つが背骨です。翻訳と行き先の評価を合わせると、元の系の停止性が
1 行で出ます。

```lean
example (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO
```

### 新しい系が出すもの

`Rewrite` の 3 つのフィールド。停止性を証明したいなら、さらに測度 1 つ。
測度の行き先は、整礎関係の入った型なら何でもよい（`Nat`、順序数、自作の項）。
一歩ごとに狭義に下がることを言えばよいです。

## ビルド

```sh
lake build
```

Lean 4 v4.30.0。依存は 2 つ。mathlib と、BMS の停止性証明のための
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern)。

`Googology.Core` は core Lean の外を何も import しません。だから停止性の道具一式は
mathlib 無しで読めて使えます。mathlib が入るのは、表記系が順序数へ評価する場所だけで
あります。今のところ `Googology.Notation.ExBuchholz.Ord` です。

## 状態

`Core/` は完成。`Notation/ExBuchholz` は表記系として完成しており、`OTLt_wf` に
仮定は要りません。`Notation/BMS` はどの行数でも停止します。`Trans/` は空です。
`sorry` も追加公理もありません。

## ライセンス

MIT ライセンスです。詳しくは [LICENSE](LICENSE) をご覧ください。
