[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Notation

表記系ごとに 1 ディレクトリ。表記系とは、項の型と、その上の順序と、たいていは
基本列を持つもののことです。

全部ここに置きます。巨大数の側で定義された系（BMS、DBMS、Y）も、証明論の文献から
来た系（Buchholz の `OT_B`、Rathjen の `T(M)`）も同じ種類のものなので、分けません。

## 規則

**表記系は他の表記系を import しません。** ここのディレクトリは自分自身と
`Googology/Core` しか知りません。2 つの系を結びつけるものは全部
[Trans](../Trans/README-ja.md) に置きます。

これで import の向きが保たれる。翻訳を `BMS/` の下に置くと、BMS を import
しただけで翻訳先の系が全部付いてきて、最後にはライブラリ全体が付いてきます。

## 系ごとのファイル（推奨）

| ファイル | 中身 |
|---|---|
| `Basic.lean` | 項あるいは状態の型と、その上の順序 |
| `Expand.lean` | 展開規則または基本列。バージョンごとに `Rewrite` の値を 1 つ |
| `Std.lean` | 標準形と生成元（`Rewrite.Std`） |
| `Eval.lean` | 順序への評価。あれば（`Eval`） |
| `WF.lean` | 整礎性。借りてくるのではなくここで証明する場合 |

バージョンが複数ある系——BMS の BM4 / 3.3 / 2 / 1.1——は、同じ項型の上に
バージョンごとの `Rewrite` の値を定義します。`Rewrite` を型クラスではなく
構造体にしてあるのはこのためです。

## 依存

`Googology/Core` は core Lean 以外に依存しません。mathlib は**系ごとに**
import します。順序数へ評価する系だけが import するのであって、このディレクトリ
全体が依存するのではありません。構文的な順序だけで済む系は mathlib 非依存のままに
なります。

## 索引

| 系 | 項 | 順序 | 標準形 | `Rewrite` | `Eval` |
|---|---|---|---|---|---|
| [ExBuchholz](ExBuchholz/README-ja.md) | 済 | 狭義線形順序 | 決定可能。較正は未 | — | — |
