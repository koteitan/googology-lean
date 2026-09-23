[← Back](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# WellOrder

1-Y の展開が整礎であることの証明。Lean 4.33.1 の二つのプロジェクトから Lean 4.30.0
と Mathlib v4.30.0 へ移植した。`../WellFounded.lean` がこれを `../Basic.lean` の
`expand` に使う。

## 出どころ

| ディレクトリ | ファイル数 | 出どころ | ライセンス |
|---|--:|---|---|
| `ZeroY/` | 42 | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) の `ZeroY/`。そこで [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) の `formalization/ZeroY` から翻案したもの | Apache-2.0 |
| `OneY/` | 118 | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) の `OneY/`。そこで Phyrion1343/1Y-Well-Ordering-Lean の `formalization/OneY` から翻案したもの | Apache-2.0 |
| `Por/` | 16 | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) の `Por/`。意味の層のモデルと、BMS の層 `Por/BMS/` | Apache-2.0 |
| `Equiv/` | 27 | [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) の `Equiv/`。書き起こしが Phyrion 氏の展開と同じであることの証明 | MIT |
| `Port.lean` | 1 | 新規。移植で使うタクティク `strip_mdata` | MIT |

revision は 1y-wo-por が `db86f2d`、1y-expand-equiv が `c9a5368` である。
取り込んだのは、最後の二つの定理が必要とするモジュールだけである。`ZeroY/`、
`OneY/`、`Por/` は全部、`Equiv/` は `Yukito.lean` と `YukitoCheck.lean` を除く全部で
ある。`Equiv/Yukito.lean` の代わりに、同じコードの `../Yukito.lean` を使う。

Apache-2.0 のファイルはヘッダをそのまま残す。ライセンスの本文は
[LICENSE-APACHE](../../../../LICENSE-APACHE)、出どころの記録は
[NOTICE](../../../../NOTICE) にある。

## 移植で変えたこと

* import のモジュール名に接頭辞 `Googology.Notation.Y.WellOrder.` を付けた。
  `Equiv.Yukito` を import していた 2 個のファイルは `OneY.Extraction` も import する。
  `Equiv/Yukito.lean` はこれを import していたが、`../Yukito.lean` はしない。
* どのファイルにも、移植したことを書いたヘッダの行がある。証明を変えたファイルは、
  何を変えたかも書く。そういうファイルは 7 個ある。4 個では、Lean 4.30.0 で
  `omega` が 1〜3 か所通らないので、補題に替えるか、前に `strip_mdata` を置いた。
  `OneY/Expansion.lean` では `by decide` を `Nat.one_pos` に替えた。
  `Equiv/Search.lean` では、ゴールを先にベータ簡約する。`Equiv/Row0.lean` は次の項目
  にある。
* `Equiv/Row0.lean` は、1y-expand-equiv がライセンスの無い `YesMetaZFC.BMS` を
  使っていたところで `Por.BMS` を使う。`Por.BMS.greatestBelow?` は再帰で定義されて
  いないので、そこの証明の一つは `greatestBelow?_succ` で展開する。
* `Equiv/` のファイルは、書き起こしが今ある `Googology.Notation.Y` を open する。
  名前空間 `ZeroY`、`OneY`、`Por`、`Yukito` はそのまま残す。

## 使う二つの定理

```lean
-- Por/WellOrdering.lean
theorem Por.expansion_wellFounded :
    WellFounded (ZeroY.ExpansionStep OneY.Numeric.expand)

-- Equiv/Lower.lean
theorem Yukito.expand_eq (s : List Nat) (hs : ZeroY.Legal s) (N m efuel : Nat)
    (hm : sequenceBound s ≤ m) (hml : s.length ≤ m) (hef : sequenceBound s ≤ efuel)
    (hn : 0 < s.length) :
    expandOut (expandJS N (m + 1) efuel (calcMountain s (m + 1))) = expandValues s hs N
```

`ZeroY.ExpansionStep e t s` は、ある $`N`$ で $`t = e(s, N)`$ かつ $`t \ne s`$ という
意味である。どちらも依存する公理は `propext`、`Classical.choice`、`Quot.sound` だけで
ある。
