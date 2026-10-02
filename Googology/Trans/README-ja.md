[← Back](../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans

具体的な翻訳。2 つの系を同時に import する唯一の層。

## 規則

```
Trans/<A>/<B>/      翻訳 A → B
Trans/<A>/common/   2 つ以上の翻訳が使う、A だけについての事実
Trans/common/       いくつもの系が共有する事実（今は無い）
```

- 向きごとにディレクトリを 1 つ置く。`Trans/<A>/<B>/` は
  [一番上の README](../../README-ja.md) の表のセル「A → B」であり、そのセルの目標
  （単射、順序を保つ、…）をそこで証明する。`B → A` は `Trans/<B>/<A>/` に置く。
  `BMS/ExBuchholz/` は行列を順序数として読み、`ExBuchholz/BMS/` は順序数のトリオ行列を作る。
- 同じ系の仲間の中の翻訳（原始数列 → ペア数列、`r` 行 → `r + 1` 行）は
  `Trans/<A>/<A>/` に置く。
- 往復のように両方向が使うものは、先にそれを定義する向きに置き、もう片方から import する。
- `A` だけについてのファイルは、2 つ以上の翻訳が使うなら `Trans/<A>/common/` に、
  1 つだけが使うならそのディレクトリに置く。
- 育ったディレクトリは行数で分ける（2 行は `PSS/`、3 行は `Trio/`）。
- どのディレクトリにも README を置き、ファイルと、それぞれが何を証明するかを並べる。
  下の表からたどれる。

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
| [BMS/common/](BMS/common/README-ja.md) | 複数の翻訳が使う、BMS だけについての事実。成分列の上の展開（行数によらない）、切り取りと継ぎ足し、3 行の展開の共終性（`TrioCof/`）。 |
| [BMS/BMS/](BMS/BMS/README-ja.md) | BMS → BMS。原始数列がペア数列の中に入ること、`r` 行が `r + 1` 行の中に入ること（下に 0 の行を足す）。 |
| [BMS/ExBuchholz/](BMS/ExBuchholz/README-ja.md) | BMS → 拡張ブーフホルツ ψ。行列がどの順序数を名指すか。1 行（ε₀ 未満、ε 数、ζ₀、階数 = 値）と、ペア数列（階数 = 1 + val、`PSS/`）。 |
| [BMS/PoR/](BMS/PoR/README-ja.md) | BMS → Carlson のパターン。2 行（`PSS/`）: 写像は順序を保ち、R₁⁺ の核から 0 を除いたものへの全射。Lean で証明済み。3 行（`Trio/`）: プログラム `por/phi3def2.py` と紙の上の証明。 |
| [PoR/InaccPsi/](PoR/InaccPsi/README-ja.md) | パターン → InaccPsi の項。ω 個の弱到達不能基数の上の表記系の可算な部分が R₂⁺ の核を覆う、という Wilken の主張について：正確な命題、可算な値が始切片になること（Lean）、υ_{ω·ω} 未満のどの順序数も Carlson の R₂ の核に入ること（紙の上、査読済み）、補題の木としての道筋、実験。 |
| [ExBuchholz/BMS/](ExBuchholz/BMS/README-ja.md) | 拡張ブーフホルツ ψ → BMS。`ψ_0(Ω_α)` のトリオ行列（`Trio/`）: 規則 1〜10 とその直し、`ψ_0(Ω_2)` 未満での標準形と順序、シートとの突き合わせ。 |
| [DBMS/common/](DBMS/common/README-ja.md) | 複数の翻訳が使う、DBMS だけについての事実。 |
| [DBMS/DBMS/](DBMS/DBMS/README-ja.md) | DBMS → DBMS。`r + 1` 行が `r + 2` 行の中に入ること。 |
| [DBMS/BMS/](DBMS/BMS/README-ja.md) | DBMS → BMS。成分列の上の 1 行、ブロックとその標準形の並び、3 行 DBMS と 3 行 BMS の比較（`ThreeRow*`）。 |
| [DBMS/ExBuchholz/](DBMS/ExBuchholz/README-ja.md) | DBMS → 拡張ブーフホルツ ψ。1 行と 2 行の順序数、1 行 DBMS の表のセル。 |
