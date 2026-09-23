[← Back](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# Y

Y 数列（1-Y）を展開系として置く。

## 定義の出どころ

Y 数列は Yukito 氏のものである。公式の定義はプログラムである。
[wiki の記事](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97)は展開を
概略しか書かず、[Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の
[`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js)
を定義として挙げている。

`Yukito.lean` はそのプログラムを文ごとに Lean へ書き起こしたものである。疎配列、
添字の計算、ループを `break` する位置をそのまま保つ。書き起こしは koteitan の
[koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv/blob/c9a5368a09ceb62ec671a6c3447a4719d035dfc0/Equiv/Yukito.lean)
（revision `c9a5368`）のものである。コードは変えていない。注釈は英語に訳し、
使っていない import を一つ落とした。

## ファイル

| ファイル | 中身 |
|---|---|
| `Yukito.lean` | 書き起こし。`calcMountain`、`calcDiagonal`、`getBadRoot`、`expandJS`、`expandOut` |
| `Basic.lean` | 燃料を固定した `expand s n`、種 `(1, h+1)` から到達できる標準形 `YStd`、展開系 `ySys` と種 `yStd` |
| `WellFounded.lean` | 下の停止性の定理 |
| `WellOrder/` | その定理が使う証明。Lean 4.33.1 の二つのプロジェクトから移植した。[WellOrder/README-ja.md](WellOrder/README-ja.md) にある |

`test/YCheck.lean` は `expand` を `script.js` 自身の出力と 213 件で比べる。種
`(1,2)`、`(1,3)`、`(1,4)` から `n = 1, 2, 3` の展開を 3 回まで行って届く、項数 9
以下の列の全部と、`(1,2,4,8,10,8)` を含む 16 個の列である。213 件すべて一致する。
これは書き起こしとプログラムの照合であって、証明ではない。

## 停止性

列 $`s = (s_0, \dots, s_{l-1})`$ が次を満たすとき、*合法*（`ZeroY.Legal s`）と呼ぶ。

```math
\forall i \lt l,\ s_i \gt 0 \quad\text{かつ}\quad (l = 0 \lor s_0 = 1).
```

標準形はすべて合法である（`YStd.legal`）。`expand s n` を $`s[n]`$ と書く。

| 名前 | 主張 |
|---|---|
| `expand_eq_numeric` | 合法な $`s`$ の上で、$`s[n]`$ は Phyrion 氏の展開 `OneY.Numeric.expand` に等しい |
| `ySys_wf` | $`\neg \exists (s_i)_{i \in \mathbb{N}},\ \forall i,\ \mathrm{YStd}(s_i) \land s_i \ne () \land \exists k,\ s_{i+1} = s_i[k]`$ |
| `ySys_terminates`、`yStd_terminates` | 標準形から始めると、括弧をどう選んでも $`()`$ に着く |
| `yLegal_wf`、`yLegal_terminates` | 同じ二つを、標準形かどうかによらず合法な列すべての上で（`yLegal`） |
| `expand_terminates` | $`f : \mathbb{N} \to \mathrm{List}\ \mathbb{N}`$ で $`f(0)`$ が合法、$`\forall n\ \exists k,\ f(n+1) = f(n)[k]`$ なら $`\exists n,\ f(n) = ()`$ |
| `yEval` | 展開の階数。一歩ごとに真に減る順序数の測度 |
| `yStd_iff_generated` | 標準形は、Phyrion 氏の形式化が種から生成する列と同じである |
| `yStd_strictWellOrder` | 辞書式順序（真の前半部分が小さい）は標準形の上の狭義整列順序である |

`sorry` は無い。公理は `propext`、`Classical.choice`、`Quot.sound` だけである。

非標準の系は `yLegal` で、状態は合法な列すべてである。0 を含む列や、先頭が `1` で
ない列については何も証明していない。

## 証明の出どころ

証明は Lean 4.33.1 の二つのプロジェクトで、`WellOrder/` に Lean 4.30.0 へ移植した。

* [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) が
  `Por.expansion_wellFounded` を証明している。`OneY.Numeric.expand` の自明でない
  一歩は、合法な列すべての上で整礎な関係である。組合せの部分は
  [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)
  （Apache-2.0）からの翻案である。意味の部分は、Phyrion 氏の構成可能宇宙と
  許容順序数の代わりに、patterns of resemblance の形の順序数上の関係を使う。
* [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) が
  `Yukito.expand_eq` を証明している。空でない合法な列の上で、ここの書き起こし
  （`expand` の燃料で）は Phyrion 氏の `expandValues` と同じ関数である。

`WellFounded.lean` が二つをつなぐ。二つが使う書き起こしは `Yukito.lean` である。
移植した `Equiv/` のファイルは、自前の写しの代わりにこれを import する。

`expand` の燃料は `expand_eq` が求めるものである。山を作る燃料が
`m + 1`（`m = bound s + length s`）、抽出の燃料が `bound s` で、`bound s` は最大の
項（ただし `1` 以上）である。
