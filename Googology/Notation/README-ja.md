[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Notation

表記系ごとに 1 ディレクトリ。表記系とは、項の型と、その上の順序と、たいていは
基本列を持つもののことである。

全部ここに置く。巨大数の側で定義された系（BMS、DBMS、Y）も、証明論の文献から
来た系（Buchholz の `OT_B`、Rathjen の `T(M)`）も同じ種類のものなので、分けない。

## 規則

**表記系は他の表記系を import しない。** ここのディレクトリは自分自身と
`Googology/Core` しか知らない。2 つの系を結びつけるものは全部
[Trans](../Trans/README-ja.md) に置く。

これで import の向きが保たれる。翻訳を `BMS/` の下に置くと、BMS を import
しただけで翻訳先の系が全部付いてきて、最後にはライブラリ全体が付いてくる。

## 系ごとのファイル（推奨）

| ファイル | 中身 |
|---|---|
| `Basic.lean` | 項あるいは状態の型と、その上の順序 |
| `Expand.lean` | 展開規則または基本列。バージョンごとに `Rewrite` の値を 1 つ |
| `Std.lean` | 標準形と生成元（`Rewrite.Std`） |
| `Eval.lean` | 順序への評価。あれば（`Eval`） |
| `WF.lean` | 整礎性。借りてくるのではなくここで証明する場合 |

バージョンが複数ある系——BMS の BM4 / 3.3 / 2 / 1.1——は、同じ項型の上に
バージョンごとの `Rewrite` の値を定義する。`Rewrite` を型クラスではなく
構造体にしてあるのはこのためである。

## 依存

`Googology/Core` は core Lean 以外に依存しない。mathlib は**系ごとに**
import する。順序数へ評価する系だけが import するのであって、このディレクトリ
全体が依存するのではない。構文的な順序だけで済む系は mathlib 非依存のままに
なる。

## 索引

| 系 | 項 | 順序 | 標準形 | `Rewrite` | `Eval` |
|---|---|---|---|---|---|
| [ExBuchholz](ExBuchholz/README-ja.md) | 済 | 狭義線形順序 | 決定可能。較正は未 | `exbOT` | `exbOTEval` |
| [BMS](BMS/README-ja.md) | 配列 | パッケージ側の比較 | 階段から到達可能 | `bms r` | `bmsEval`（階数）、`r = 1` では `Trans.BMS.bmsOrdEval` |
| [DBMS](DBMS/README-ja.md) | 配列 | BMS と同じ | `dstair` から到達可能 | `dbms r` | `r = 1` では `Trans.DBMS.dbmsOrdEval` |
