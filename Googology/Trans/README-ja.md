[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans

具体的な翻訳。2 つの系を同時に import する唯一の層。

## 規則

```
Trans/<from>/<to>/     系 <from> と <to> の間の翻訳
Trans/<from>/common/   2 つ以上の <to> が使う、<from> だけについての事実
Trans/common/          いくつもの <from> が共有する事実（今は無い）
```

- `<from>` は解析する系、`<to>` はそれを測る系である:
  `BMS/ExBuchholz/`、`BMS/PoR/`、`DBMS/BMS/`、`DBMS/ExBuchholz/`。
- 対ごとにディレクトリを**1 つ**置く。方向ごとには分けない。両方向の模倣と、
  あれば `Equiv` を同じ場所に置く。そうしないと `Equiv` の置き場所が決まらず、
  2 つの方向が離れていく。
- `<from>` だけについてのファイルは、2 つ以上の `<to>` が使うなら
  `<from>/common/` に、1 つの `<to>` だけが使うならその `<to>` に置く。
- 育ったディレクトリは行数で分ける（2 行は `PSS/`、3 行は `Trio/`）。
- どの `<from>/<to>/` と `<from>/common/` にも README を置き、ファイルと、それぞれが
  何を証明するかを並べる。下の表からたどれる。

系は全部 [Notation](../Notation/README-ja.md) にあるので、巨大数の系から
証明論の系への翻訳も、他の対と何も変わらない。

## どれを作るか

仕事が済む範囲で一番弱いものを選ぶ。

| 構造 | 要求 | 得られるもの |
|---|---|---|
| `Sim` | 一歩が一歩に写る | 整礎性と停止性が移る |
| `StepHom` | 展開と可換、＋停止状態の対応 | `Sim` になる |
| `Equiv` | 互いに逆な `Sim` | 両側が同値 |
| `OrdHom` | 順序を保つだけ | 整礎性が移る |

`StepHom` は括弧の番号を付け替える `reindex : Nat → Nat` を持つ。付け替えない
なら `id` を入れる。

## 較正は定理ではない

参照実装との一致は有限個の検査（`#guard`、`decide`）であって、全入力についての
証明ではない。別ファイルに置き、上の定理と同列に読まれないようにする。

## 索引

各ディレクトリの README に、ファイルごとの中身を載せる。

| ディレクトリ | 何を証明するか |
|---|---|
| [BMS/common/](BMS/common/README-ja.md) | 複数の翻訳が使う、BMS だけについての事実。成分列の上の展開（行数によらない）、0 の行、切り取りと継ぎ足し、3 行の展開の共終性（`TrioCof/`）。 |
| [BMS/ExBuchholz/](BMS/ExBuchholz/README-ja.md) | BMS ↔ 拡張ブーフホルツ ψ。行列の階数を ψ の値で与える（1 行、ε 数、ζ、ペア数列: 階数 = 1 + val、`PSS/`）。ψ をトリオ数列に写す規則（`Trio/`）。 |
| [BMS/PoR/](BMS/PoR/README-ja.md) | BMS → Carlson のパターン。2 行（`PSS/`）: 写像は順序を保ち、R₁⁺ の核から 0 を除いたものへの全射。Lean で証明済み。3 行（`Trio/`）: プログラム `por/phi3def2.py` と紙の上の証明。 |
| [DBMS/common/](DBMS/common/README-ja.md) | 複数の翻訳が使う、DBMS だけについての事実。 |
| [DBMS/BMS/](DBMS/BMS/README-ja.md) | DBMS ↔ BMS。1 行、ブロックとその標準形の並び、3 行 DBMS と 3 行 BMS の比較（上界、`ThreeRowUpper*`）。 |
| [DBMS/ExBuchholz/](DBMS/ExBuchholz/README-ja.md) | DBMS → 拡張ブーフホルツ ψ。1 行と 2 行、表。 |
