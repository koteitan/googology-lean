[← Back](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# OmegaY

公式の ω-Y 数列を展開系として置く。

## 定義の出どころ

ω-Y 数列は Yukito 氏のものである。公式の定義はプログラムである。Naruyoko 氏の
[StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence/blob/b26ba7e5fc2c8edb4065f1d721855a7e0e644ff2/script.js)
の `expand`（revision `b26ba7e`、v1.1、既定の設定）である。このプログラムにはライセンスの
ファイルが無い。

`Official.lean` はこのプログラムの書き起こしではない。
[koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) で、山の言葉で書いた規則の説明
[`notes/03-official-rule.md`](https://github.com/koteitan/wy-wo-por/blob/7038635644b8d1df3f0f1a80f107210da7e33a94/notes/03-official-rule.md)
から書いたものである。プログラムは出力を比べるために動かしただけで、そのコードは使っていない。
規則は [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)
の weak-magma の展開を変えたもので、その山の上で動く。なのでこのファイルは、移植のほかの部分と
同じく Apache-2.0 である。wy-wo-por（revision `7038635`）の `OmegaY/Official/Build.lean` を
ここへ移したもので、変えたのはヘッダーとリンク 1 つだけである。`WellOrder/` の移植したファイルは
これをここから import する。

## ファイル

| ファイル | 中身 |
|---|---|
| `Official.lean` | 規則。`OmegaY.Official.expandDiagram` が $`s[n]`$ の山を作り、`OmegaY.Official.expand` がその値を読む。実行できない手順はすべて明示的なエラーになる |
| `Basic.lean` | 規則の結果で、エラーのときは `()` になる `expand s n`、種 `(1, h+2)` から到達できる標準形 `OmegaYStd`、展開系 `omegaYSys` と種 `omegaYStd`、すべての列の上の `omegaYAll` |
| `WellFounded.lean` | 下の停止性の定理 |
| `WellOrder/` | その定理が使う証明。Lean 4.33.1 のプロジェクトから移植した。[WellOrder/README-ja.md](WellOrder/README-ja.md) にある |

`test/OmegaYCheck.lean` は、公式のプログラムから記録した展開 $`s[n] = t`$ を 474 件持つ。
$`n = 1, 2, 3`$ で、`(1,3,3)`、`(1,4,4)`、`(1,4)`、`(1,4,6,4)`、`(1,3,4,3)`、weak-magma の規則が
食い違う 3 つの列、wy-wo-por の標本の標準形、長さ 5 以下で項が 7 以下の合法な列である。
各件で、規則が `.ok t` を返すこと、規則が作る山が $`t`$ の正準の山であること、$`t`$ が
$`s`$ より辞書式で小さいことを `#guard` で確かめる。474 件すべて一致する。これは規則と
プログラムの照合であって、証明ではない。

## 規則のエラー

プログラムにはエラーが無い。Lean の規則には、想定した手順が実行できないときのエラーがある。
確かめた 474 件では一度も起きないが、標準形で起きないことは証明していない。`expand` は
エラーを `()` と読む。`()` は止まる状態である。$`(1)[n] = ()`$ なので `()` はもともと標準形で、
標準形に新しい状態は増えない。

## 停止性

`expand s n` を $`s[n]`$ と書く。

| 名前 | 主張 |
|---|---|
| `official_wf` | 自然数の列すべての上の関係 $`t \prec s \iff s \ne () \land \exists n,\ \mathtt{Official.expand}\ s\ n = \mathtt{ok}\ t`$ は整礎である |
| `no_infinite_official_chain` | $`\neg \exists (s_i)_{i \in \mathbb{N}},\ \forall i,\ s_i \ne () \land \exists n,\ \mathtt{Official.expand}\ s_i\ n = \mathtt{ok}\ s_{i+1}`$ |
| `omegaYSys_wf` | $`\neg \exists (s_i)_{i \in \mathbb{N}},\ \forall i,\ \mathrm{OmegaYStd}(s_i) \land s_i \ne () \land \exists k,\ s_{i+1} = s_i[k]`$ |
| `omegaYSys_terminates`、`omegaYStd_terminates` | 標準形から始めると、括弧をどう選んでも $`()`$ に着く |
| `omegaYAll_wf`、`omegaYAll_terminates` | 同じ二つを、標準形かどうかによらず自然数の列すべての上で（`omegaYAll`） |
| `expand_terminates` | $`f : \mathbb{N} \to \mathrm{List}\ \mathbb{N}`$ で $`\forall n\ \exists k,\ f(n+1) = f(n)[k]`$ なら $`\exists n,\ f(n) = ()`$ |
| `omegaYEval` | 展開の階数。一歩ごとに真に減る順序数の測度 |

`sorry` は無い。公理は `propext`、`Classical.choice`、`Quot.sound` だけである。

非標準の系は `omegaYAll` で、状態は自然数の列すべてである。条件は無い。規則がエラーを返す列では、
一歩で $`()`$ へ行く。

## 証明の出どころ

証明は Lean 4.33.1 のプロジェクト [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por)
（revision `7038635`）で、`WellOrder/` に Lean 4.30.0 へ移植した。そこでは
`OmegaY.Official.Recon.FinalStageF.wellFounded_step` を証明している。`OmegaY.Official.expand`
の自明でない一歩は、列すべての上で整礎な関係である。組合せの部分（正準の山、展開の仕組み、森、
キー、反映のインターフェース）は
[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)
（Apache-2.0）からの翻案である。意味の部分は、Phyrion 氏の反映の代わりに、patterns of
resemblance の形の順序数上の関係を使う。必要な 0-Y のモジュールは、Y 数列のために移植済みの
ものを [`../Y/WellOrder/`](../Y/WellOrder/README-ja.md) から import する。

`WellFounded.lean` は、この定理を `Basic.lean` の `expand` と展開系の言葉で言い直す。
