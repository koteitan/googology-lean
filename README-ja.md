[English](README.md) | [Japanese](README-ja.md)

# googology-lean

巨大数のための Lean 4 ライブラリ。展開系、順序数表記系、その間の翻訳を扱う。

BMS、DBMS、Y 数列などの巨大数の表記では、展開をくり返すと必ず有限回で止まるか
（整礎性）が問題になる。このライブラリは、整礎性を示すための共通の枠組みを用意している。
各表記は、その表記に固有の部分だけを定義して証明すればよい。

koteitan と Phyrion による形式証明のリンク集は [portal/](portal/README-ja.md) にある。

## 何が証明されているか

どの表記にも同じ目標を立てて証明する。目標の正確な定義は [spec-ja.md](spec-ja.md) の 6 節にある。

| 表記 | 展開の定義 | 整礎性 | 整礎性(非標準) |
|---|:-:|:-:|:-:|
| BMS | ✅ | ✅ | ✅ |
| DBMS | ✅ | ✅ | ✅ |
| Y 数列 | ✅ | ✅ | ✅ |
| ω-Y（公式） | ✅ | ✅ | ✅ |
| 拡張ブーフホルツ ψ | ✅ | ✅ |  |

- 展開の定義：展開を Lean の関数として書き、実際に計算できる。
- 整礎性：標準形の上の展開の関係に無限降下列が無い。停止性（どの展開列も有限で止まる）と同値で、それも証明してある。
- 整礎性(非標準)：標準形でない状態も含めた全体の上で、同じことが成り立つ。
- Y 数列では「全体」は合法な列すべてを指す。合法とは、項がすべて正で、空でなければ先頭が `1` であること。証明は [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) と [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) から移植した。[Notation/Y](Googology/Notation/Y/README-ja.md) にある。
- ω-Y（公式）は、公式のプログラム [Naruyoko/StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence) の `expand` の展開を持つ ω-Y 数列である。ここでは「全体」は自然数の列すべてを指し、条件は無い。Lean の規則は、想定した手順が実行できないときエラーを返し、そのとき一歩は `()` へ行く。プログラムと照合した 474 件の展開ではエラーは起きないが、標準形で起きないことは証明していない。証明は [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) から移植した。[Notation/OmegaY](Googology/Notation/OmegaY/README-ja.md) にある。

### 順序数への翻訳写像

各状態に、それが名指す順序数を割り当てる写像。

| 表記 | 定義 | 単射性 | 全射性 | 展開で値が下がる | 階数と一致 | 順序を保つ |
|---|:-:|:-:|:-:|:-:|:-:|:-:|
| 2 行以下の BMS | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 3 行以上の BMS |  |  |  |  |  |  |
| 1 行の DBMS | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 2 行の DBMS | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| 3 行以上の DBMS |  |  |  |  |  |  |
| Y 数列 |  |  |  |  |  |  |
| ω-Y |  |  |  |  |  |  |
| 拡張ブーフホルツ ψ | ✅ | ✅ | ✅(*1) | ✅ | ✅ | ✅ |

- 定義：写像を Lean で定義してある。原始数列と 1 行の DBMS では、拡張ブーフホルツ ψ の項に読んでその値を取る。ペア数列では、[koteitan/pss-proof](https://github.com/koteitan/pss-proof) の `Trans` で Buchholz 項に写し、拡張ブーフホルツ項に写して `1 + val` を取る（空列は 0）。2 行の DBMS では、標準形を `(0,0)` で始まるブロックに分け、各ブロックの残りをペア数列 `M_i` に読んで、`w^o(M_0) + w^o(M_1) + ...` を取る（`o` はペア数列の順序数）。拡張ブーフホルツ ψ では項の値そのもの。
- 単射性：異なる標準形は異なる順序数に写る。BMS と DBMS では標準形は行列そのものなので、二つの状態は行列として、つまり成分で比べる。
- 全射性：像がちょうど分かっている。原始数列と 1 行の DBMS では `e0` 未満の順序数全部、ペア数列と 2 行の DBMS では `p0(W_w)` 未満の順序数全部、拡張ブーフホルツ ψ では `p0(Λ)` 未満の順序数全部（*1）。
- (*1) 拡張ブーフホルツ ψ の状態は `W` 未満の標準形の項なので、像は `C_0(Λ)` 全部ではなく、その `W` 未満の部分、つまり `p0(Λ)` 未満の順序数全部である。
- 展開で値が下がる：一回展開すると値が真に小さくなる。
- 階数と一致：値が展開の階数（展開で降りられる高さ）に等しい。こうなる写像は一つしかない。
- 順序を保つ：状態の順序と順序数の順序が一致する。

### 表記の間の翻訳写像

| 翻訳元＼翻訳先 | 原始数列 | ペア数列 | トリオ数列 | BMS `r` 行 | BMS `r+1` 行 | 1 行の DBMS | DBMS `r` 行 | DBMS `r+1` 行 | 拡張ブーフホルツ ψ |
|---|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| 原始数列 | — | ✅✅✅✅❌✅ |  |  |  |  |  |  | ✅✅✅✅✅✅ |
| ペア数列 |  | — |  |  |  |  |  |  | ✅❌❌✅✅✅(*2) |
| トリオ数列 |  |  | — |  |  |  |  |  |  |
| BMS `r` 行 |  |  |  | — | ✅✅✅✅❌✅(*4) |  |  |  |  |
| BMS `r+1` 行 |  |  |  |  | — |  |  |  |  |
| 1 行の DBMS | ✅✅✅✅✅✅ |  |  |  |  | — |  |  |  |
| DBMS `r` 行 |  |  |  | ✅✅✅✅❌✅ |  |  | — | ✅✅✅✅❌✅(*3) |  |
| DBMS `r+1` 行 |  |  |  |  |  |  |  | — |  |
| 拡張ブーフホルツ ψ |  |  | ✅❌❌✅❌❌ |  |  |  |  |  | — |

- 行が翻訳元、列が翻訳先である。空のマスは、まだ翻訳写像を定義していない組である。
- 各マスの 6 つの印は、左から順に「定義、展開を保つ、展開と可換、単射性、全射性、階数を保つ」である。✅ は証明済み、❌ はまだである。
- BMS `r` 行 → BMS `r+1` 行は、任意の `r` についての一つの写像である。DBMS `r` 行 → BMS `r` 行の翻訳先は、標準形に限らない全配列である。拡張ブーフホルツ ψ → トリオ数列は、`p0(W_a)` の形の項だけの写像である。
- 定義：写像を Lean で定義してある。原始数列 → 拡張ブーフホルツ ψ の翻訳先は `p0(W)` 未満の標準形、ペア数列 → 拡張ブーフホルツ ψ の翻訳先は `p0(W_w)` 未満の標準形である。原始数列 → ペア数列、BMS `r` 行 → `r+1` 行、DBMS `r` 行 → `r+1` 行は、下に 0 の行を足す写像である。トリオ数列への写像は `a < e0` の範囲で定義してある。拡張ブーフホルツ ψ → トリオ数列は [koteitan/trio](https://github.com/koteitan/trio) の写像の書き起こしである。`a < e0` では、像が 3 行の BMS の標準形であること（`trioMatrix_std`）と、順序を保ち、順序を反映すること（`omegaIndexMatrix_lt_iff`）を証明してある。`e0 <= a < Λ` の規則 1〜10 は書き起こして（`TrioRules.lean`）、公開されている対応表と照合した。添字が 0 か 1 だけの項（どれも `p0(W_2)` 未満）で深さが 200 以下なら、規則 1〜10 は標準形を出し、順序を保ち、順序を反映する（`TrioTreeRules.lean`）。
- (*2) ペア数列 → 拡張ブーフホルツ ψ の「展開を保つ」と「展開と可換」は偽である（反証済み）。生成元 `(0,0)(1,1)` を `[0]` で展開すると `(0,0)` になり、それぞれ `p0(W_1)` と `1` に写る。`p0(W_1)` の基本列の項は `1` にならない（`Trans/PSS/Expansion.lean`）。ただし 1 手は、拡張ブーフホルツ ψ の側の 1 手以上に写る。「何手かで届く」は写像で両方向に保たれる（`pairToExb_transGen_iff`、`Trans/PSS/Steps.lean`）。例：`(0,0)(1,1)[0]` は `p0(W_1) →[0] w →[1] 1` に写る。その手数に上限は無い。`(0,0)...(p,p)(p+1,p)[0]` はちょうど `p+1` 手に写る（`pairToExb_steps_unbounded`、`pairToExb_min_steps`）。
- (*3) DBMS `r` 行 → DBMS `r+1` 行は全射でない（反証済み）。像の最下行はすべて 0 だが、生成元 `(0,0)(1,0)(2,1)` はそうでない（`dbmsToSucc_not_surjective`）。
- (*4) BMS `r` 行 → BMS `r+1` 行は全射でない（反証済み）。像の最下行はすべて 0 だが、生成元 `(0,0)(1,1)` はそうでない（`bmsToSucc_not_surjective`）。
- 展開を保つ：一回の展開が、翻訳先でも一回の展開に写る。
- 展開と可換：括弧の番号まで含めて、展開してから写しても、写してから展開しても同じになる。
- 単射性・全射性：翻訳先の標準形に対して。原始数列 → 拡張ブーフホルツ ψ は両方を満たし、二つの系は同じ系の書き換えになる。1 行の DBMS → 原始数列も両方を満たす。1 行の DBMS の標準形の行列は、原始数列そのものである。
- 階数を保つ：翻訳の前後で階数が等しい。
- 途中の補題を含む定理の一覧は [results-ja.md](results-ja.md) にある。


## 使い方

`lakefile.toml` に足す。

```toml
[[require]]
name = "googology"
git = "https://github.com/koteitan/googology-lean"
```

たとえば次のように使える。

```lean
import Googology

open Googology Notation.BMS

-- 5 行のバシク行列は停止する。
example : (bms 5).Terminates := bms_terminates 5
```

## 考え方

展開系は状態の型そのものをフィールドに持つ。だから型の違う系が 1 つの命題を共有
できる。

```lean
structure Rewrite where
  State  : Type
  step   : State → Nat → State
  halted : State → Prop
```

型クラスではなく構造体にしてあるのは意図的である。1 つの状態型に複数の展開規則が
乗るため（BMS の BM4 / 3.3 / 2 / 1.1）で、状態型を鍵にした型クラスでは 1 つしか
持てない。

### 一度だけ証明して、全系が使うもの

| 名前 | 主張 |
|---|---|
| `Rewrite.terminates_of_wf` | 整礎性 ⟹ 停止性 |
| `Rewrite.wf_of_measure` | 任意の整礎順序への測度 ⟹ 整礎性 |
| `Rewrite.terminates_of_measure` | 測度 ⟹ 停止性 |
| `Rewrite.Std.of_terminates` | 全状態の停止性 ⟹ 標準形の停止性 |
| `OrdHom.wf` | 狭義単調な写像で整礎性が移る |
| `OrdHom.injective` | 三分律＋非反射律 ⟹ 単射 |
| `Sim.wf`、`Sim.terminates` | 模倣で整礎性と停止性が移る |
| `Sim.terminates_transfer` | 停止性が模倣に沿って手前に移る |
| `StepHom.toSim` | 展開と可換なら模倣になる |
| `Equiv.wf_iff`、`Equiv.terminates_iff` | 互いに逆な翻訳があれば両者は同値 |
| `Eval.terminates` | 整礎順序への評価 ⟹ 停止性 |
| `Eval.compOrd` | 評価 ∘ 順序を保つ写像 = 評価 |
| `Eval.ofSim` | 模倣で評価を手前に引き戻せる |
| `Rewrite.rankEval` | 整礎な系は自前の順序数の測度を持つ |

最後の 3 つが背骨である。翻訳と行き先の評価を合わせると、元の系の停止性が 1 行で
出る。

```lean
example (trans : Sim Src Tgt) (o : Eval Tgt ltO) (hO : WellFounded ltO) :
    Src.Terminates :=
  (Eval.ofSim trans o).terminates hO
```

## 系を足すには

`Rewrite` の 3 つのフィールドを与え、停止性を証明したいなら測度を 1 つ出す。測度の
行き先は、整礎関係の入った型なら何でもよい（`Nat`、順序数、自作の項）。一歩ごとに
狭義に下がることを言えば、残りは定理として受け取れる。

すでに別のところで停止性が証明されている系なら、数行で繋がる。`Notation/BMS` が
その実例。

## 中身

```
Googology/
  Core/            展開系、標準形、翻訳
  Rank.lean        整礎な系は順序数の測度を持つ
  Notation/        系そのもの
    BMS/             バシク行列。行数は任意
    ExBuchholz/      拡張ブーフホルツ ψ
    DBMS/            生成元の違う BMS
    Y/               Y 数列と、移植したその停止性の証明
    OmegaY/          公式の ω-Y 数列と、移植したその停止性の証明
  Trans/           2 つの系の間の翻訳
```

各ディレクトリに README がある。

## ビルド

```sh
lake build
```

Lean 4 v4.30.0。依存は 3 つで、mathlib と、BMS の停止性証明のための
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) と、ペア数列の翻訳写像
`Trans` のための [koteitan/pss-proof](https://github.com/koteitan/pss-proof)。
`Googology.Core` はどれも import しないので、停止性の道具一式は mathlib 無しで
読めて使える。

## 出典

このライブラリが使っている他者の成果と、使っている場所。koteitan のリポジトリは
使う場所でリンクしてあり、ここには挙げない。

| 出典 | 何を取ったか | 場所 |
|---|---|---|
| [mathlib](https://github.com/leanprover-community/mathlib4)（Apache-2.0） | 順序数、基数、その土台 | 依存。`Core` の外で import する |
| BashicuHyudora、[BASIC言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81) | バシク行列システムとその版 BM4 | `Notation/BMS/`。規則の実装は依存先の koteitan/bms-elem-pattern にある |
| Maksudov の拡張ブーフホルツ ψ。[Googology Wiki](https://googology.miraheze.org/wiki/Extended_Buchholz%27s_function) の記述 | `ψ_v(a)` と `C_v(a)` の定義 | `Notation/ExBuchholz/Ord.lean` |
| p進大好きbot、[拡張Buchholz OCFに伴う順序数表記](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E6%8B%A1%E5%BC%B5Buchholz_OCF%E3%81%AB%E4%BC%B4%E3%81%86%E9%A0%86%E5%BA%8F%E6%95%B0%E8%A1%A8%E8%A8%98) | 項、その順序、`G`、`OT`、評価、`dom` と `[ ]`、`val` が `C_0(Λ)` への同型だという主張 | `Notation/ExBuchholz/` |
| W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic 32 (1986) 195–207 | 基本列が依って立つ補題 3.2–3.6 | `Notation/ExBuchholz/FS.lean`、`Closure.lean` |
| Yukito 氏の Y 数列と、その公式プログラムである Naruyoko/YNySequence の [`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js)（revision `2de1397`） | 文ごとに書き起こした定義。検算の期待値 | `Notation/Y/Yukito.lean`、`test/YCheck.lean` |
| [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)（Apache-2.0）、revision `6533b29` | 1-Y が整礎であることの証明の組合せの層。koteitan/1y-wo-por で翻案し、ここで Lean 4.30.0 へ移植した | `Notation/Y/WellOrder/ZeroY/`、`Notation/Y/WellOrder/OneY/` |
| Yukito 氏の ω-Y 数列と、その公式プログラムである [Naruyoko/StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence/blob/b26ba7e5fc2c8edb4065f1d721855a7e0e644ff2/script.js) の `expand`（revision `b26ba7e`、v1.1、既定の設定） | 定義。koteitan/wy-wo-por で規則の説明から書いたもので、プログラムのコードは使っていない。検算の期待値 | `Notation/OmegaY/Official.lean`、`test/OmegaYCheck.lean` |
| [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)（Apache-2.0）、revision `33c16a8` | 正準の山、公式の規則のもとになった weak-magma の展開、証明のうち森、キー、反映のインターフェース。koteitan/wy-wo-por で翻案し、ここで Lean 4.30.0 へ移植した | `Notation/OmegaY/WellOrder/OmegaY/`（`Official/` を除く）、`Notation/OmegaY/Official.lean` |
| p進大好きbot、[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)。Naruyoko、[ペア数列システムの停止性証明に用いられた変換写像の全単射性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Naruyoko/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%82%B7%E3%82%B9%E3%83%86%E3%83%A0%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E%E3%81%AB%E7%94%A8%E3%81%84%E3%82%89%E3%82%8C%E3%81%9F%E5%A4%89%E6%8F%9B%E5%86%99%E5%83%8F%E3%81%AE%E5%85%A8%E5%8D%98%E5%B0%84%E6%80%A7) | ペア数列から Buchholz 項への変換写像 `Trans` とその全単射性（依存先の koteitan/pss-proof が形式化したものを使う） | `Googology/Trans/PSS/` |
| wiki の記事 [ペア数列数](https://googology.fandom.com/ja/wiki/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E6%95%B0) と [Y数列](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97) | 背景と対応表 | `memo.md` |

`Notation/Y/Yukito.lean` の書き起こしは `script.js` を Lean に訳したものである。
`Naruyoko/YNySequence` にはライセンスのファイルが無い。
`Naruyoko/StudyAndExpandSequence` にもライセンスのファイルが無い。そのコードは使っていない。
`Notation/OmegaY/Official.lean` は規則の説明から書いたもので、`test/OmegaYCheck.lean` は
プログラムの出力だけを記録している。

## ライセンス

MIT ライセンス。[LICENSE](LICENSE) を参照。

例外は `Googology/Notation/Y/WellOrder/ZeroY/`、`Googology/Notation/Y/WellOrder/OneY/`、
`Googology/Notation/Y/WellOrder/Por/`、`Googology/Notation/OmegaY/WellOrder/` の下のファイルと、
`Googology/Notation/OmegaY/Official.lean`、`test/OmegaYCheck.lean` である。これらは
[koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) と
[koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) から来たもので、Apache License 2.0
に従う。[LICENSE-APACHE](LICENSE-APACHE) と [NOTICE](NOTICE) を参照。

---

## 開発する人へ

* [spec-ja.md](spec-ja.md) — ライブラリの構成と書き方の規約。この文書群をどう書くかの
  規則も含む
* [plan-ja.md](plan-ja.md) — これからやることのツリー
* [memo-ja.md](memo-ja.md) — 議論の全体と、作業の現在地

現状：`Core/` は完成。`Notation/ExBuchholz` は表記系としても展開系としても完成
した。停止性は何も仮定せずに証明してある。`Notation/BMS` はどの行数でも停止する。
`Notation/Y` は標準形の上でも、合法な列すべての上でも停止する。
公式の ω-Y の `Notation/OmegaY` は、標準形の上でも、自然数の列すべての上でも停止する。
`Trans/` は 1 行と 2 行（ペア数列）を決着させた。どの行列についても、翻訳写像の値が
展開の階数と一致し、系全体では 1 行が `e0`、2 行が `p0(W_w)` になる。3 行から先の
読み取りは無い。何が足りないかは `plan-ja.md` にある。
