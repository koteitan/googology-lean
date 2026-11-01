[← Back](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# SSOS

Kanrokoti 氏の強2階探索表記（SSOS）を、`(0,0,2)` 未満の標準形の上で展開系として置く。

## 定義の出どころ

定義は日本語版巨大数研究 Wiki のブログ記事
[ユーザーブログ:Kanrokoti/強2階探索表記](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Kanrokoti/%E5%BC%B72%E9%9A%8E%E6%8E%A2%E7%B4%A2%E8%A1%A8%E8%A8%98?oldid=76153)
の版 76153 である。`Def.lean` がそれを書き起こしたものである。書き起こしとここの証明はすべて
[koteitan/ssosn](https://github.com/koteitan/ssosn)（revision `053b96c`、Lean 4.33.1）
のもので、Lean 4.30.0 へ移植した。

## 系

状態は自然数の列である。位置は 1 から数える。

* `step a k = Seq.fs a (k + 1)` は `a[k]` の列の部分で、良い部分の後に悪い部分を
  `k + 1` 個並べたもの。末尾が `0` なら、`k` によらずそれを取り除く。空の列で停止する。
* 生成元は `gen n`、すなわち `(0,0)` の後に `1` を `n` 個並べた列である。
* 標準形は `Standard` で、生成元を展開で閉じたもの（末尾が正なら `expand`、末尾が `0` なら
  `erase`）。`standard_iff_reach` は、これが生成元を含み `step` で閉じた最小の集合、
  すなわち [spec-ja.md](../../../spec-ja.md) の 1 章の標準形であることを示す。これらは
  `(0,0,2)` 未満の列で、項は `0` と `1` である（`standard_binary`）。`(0,0,2)` 以上の列は扱わない。

## ファイル

| ファイル | 中身 |
|---|---|
| `Def.lean` | 規則：`sp`、`mbp`、`br`、`cut` と展開 `Seq.fs` |
| `Standard.lean` | 標準形 `Standard` |
| `Tree.lean`、`Flat.lean`、`Parse.lean` | 列 `(0,0) ⌢ Y` をブロックの木に読むことと、その逆 |
| `Expansion.lean`、`Bridge.lean`、`CanonicalExpansion.lean` | 木の上の展開と、それが `Seq.fs` に一致する条件 `CutCorrect` |
| `Search.lean`、`BinarySearch.lean`、`CutReduction.lean` | `0` と `1` の列の上での規則の探索 |
| `Shape.lean`、`ShapeExpansion.lean`、`CutShape.lean` | 標準形の木の形 `StdShape` と、その上での `CutCorrect` |
| `Representation.lean`、`Top.lean` | 標準形の木。`(0,0,2)` の展開 |
| `SequenceOrdinal.lean` | 値 `o`。長さ 2 未満の列では `0` と `1`、それ以外では木の順序数 |
| `MainBelow002.lean` | 出典の形の主定理：`Below002.closure`、`decreasing`、`cofinal`、`wf`、`rank_eq` |
| `System.lean` | 系 `ssosSys`、標準形 `ssosStd`、下の定理 |

`System.lean` は出典の引き継ぎ資料にある 6 個の展開を `#guard` で確かめる。これは
書き起こしの検算であり、証明ではない。

## 定理

| 名前 | 主張 |
|---|---|
| `rel_iff` | `ssosSys` の一歩は出典の一歩の関係 `Below002.Rel` に等しい |
| `standard_iff_reach` | `Standard` は生成元を含み `step` で閉じた最小の集合 |
| `ssosStd_wf` | 標準形の上の一歩は整礎 |
| `ssos_decreasing` | 標準形の上では、一歩で `o` が真に小さくなる |
| `ssos_cofinal` | 標準な `a` と `β < o(a)` について、`a` から一歩の標準な `b` で `β ≤ o(b)` となるものがある |
| `ssos_rank` | 標準形の上では、`o` は一歩の階数に等しい |

証明していないこと：`o` が標準形の上で単射であること、像が `e0` 未満の順序数全部であること、
列の辞書式順序を保つこと。
