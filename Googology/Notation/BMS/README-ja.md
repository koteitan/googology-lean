[← Back](../../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# BMS

行数が任意のバシク行列を、展開系として表したもの。

`r = 1` は原始数列、`r = 2` はペア数列、`r = 3` はトリオ数列、以下同様です。

## 中身

```lean
noncomputable def bms (r : ℕ) : Rewrite where
  State  := Pat.StdElt r              -- r 行の標準形の行列
  step   := fun A k => expand A k     -- 括弧 1 つ分の展開
  halted := fun A => A.len = 0
```

標準形であることは状態の型が担っているので、`Rewrite.Std` に残る仕事は生成元
`(0,…,0)(1,…,1)⋯(n,…,n)` に名前を付けることだけです。

| 定理 | 主張 |
|---|---|
| `bms_Rel_iff` | 一歩の関係が、停止性証明の対象の関係と一致する |
| `bms_wf` | 一歩の展開は整礎 |
| `bms_terminates` | **どの `r` でも BMS は停止する** |
| `primitive_terminates`、`pair_terminates`、`trio_terminates` | `r = 1, 2, 3` |

## 仕事をしている場所

停止性については、ここでは何も証明していません。証明——`R_r` のラベルと Σ 初等
部分構造による、任意の行数のもの——は
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) に
にあり、このパッケージはそれを依存に持っています。このファイルがするのは `Rewrite` の
3 つのフィールドと `Subrelation.wf` 1 本を出すことだけで、残りは
`Googology.Core` が出す。

当てはまり方はぴったりです。向こうの `Pat.StdR` が、こちらの `Rewrite.Rel`
を手で書き下したものになっています。

```
StdR r A B      = 0 < B.len ∧ ∃ n, A = expand B n
(bms r).Rel A B = ¬ halted B ∧ ∃ k, A = step B k
```

これがライブラリの要点です。停止性証明を既に持っている系は数行で繋がり、
持っていない系は標準の道——測度、翻訳、評価——を無料で受け取ります。

## 状態

| | |
|---|---|
| 展開系、整礎性、停止性 | 済 |
| 生成元 | 済（`bmsStd`） |
| 順序数への評価 | 済（`bmsEval`）。一歩の展開の階数として |
| `ExBuchholz` への翻訳 | 未 |
