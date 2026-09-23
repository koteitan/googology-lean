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

`test/YCheck.lean` は `expand` を `script.js` 自身の出力と 213 件で比べる。種
`(1,2)`、`(1,3)`、`(1,4)` から `n = 1, 2, 3` の展開を 3 回まで行って届く、項数 9
以下の列の全部と、`(1,2,4,8,10,8)` を含む 16 個の列である。213 件すべて一致する。
これは書き起こしとプログラムの照合であって、証明ではない。

## よそで証明されていて、ここでは証明していないこと

**停止性はこのライブラリの定理ではない。**

* [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)
  が、1-Y が停止し整列することを Lean で証明している。対象は Phyrion 氏自身の展開
  `expandValues` で、`script.js` とは独立に定義されたアルゴリズムである。
* [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) が
  `expand_eq` を証明している。項がすべて正で先頭が `1` の列の上で、ここの書き起こし
  （`expand` の燃料で）と `expandValues` は同じ関数である。

二つを合わせると、ここで定義した展開は停止する。どちらも Lean 4.33.1 の
プロジェクトで、こちらは Lean 4.30.0 なので、どちらも import できない。だから
この主張は引用にとどめる。Phyrion 氏の形式化からは何も複製も翻案もしていない。
つながりは `Yukito.lean` が落とした import だけである。

`expand` の燃料は `expand_eq` が求めるものである。山を作る燃料が
`m + 1`（`m = bound s + length s`）、抽出の燃料が `bound s` で、`bound s` は最大の
項（ただし `1` 以上）である。
