[← Back](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# WellOrder

公式の ω-Y の展開が整礎であることの証明。Lean 4.33.1 のプロジェクトから Lean 4.30.0
と Mathlib v4.30.0 へ移植した。`../WellFounded.lean` がこれを `../Basic.lean` の
`expand` に使う。

## 出どころ

| ディレクトリ | ファイル数 | 出どころ | ライセンス |
|---|--:|---|---|
| `OmegaY/`（`OmegaY/Official/` を除く） | 180 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) の `OmegaY/`。そこで [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)（revision `33c16a8`）から翻案したもの。正準の山、展開の道具、森、キー、反映のインターフェース | Apache-2.0 |
| `OmegaY/Official/` | 310 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) の `OmegaY/Official/`。そこで書いたもの。公式の展開が整礎であることの証明 | Apache-2.0 |
| `../Official.lean` | 1 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) の `OmegaY/Official/Build.lean`。そこで書いたもの。公式の展開 `expand`。`../Basic.lean` の隣へ移した | Apache-2.0 |
| `Por/` | 3 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) の `Por/Formula.lean`、`Por/Relation.lean`、`Por/Supply.lean`。反映のインターフェースを証明する、類似パターンのモデル | Apache-2.0 |

wy-wo-por の revision は `7038635` である。取り込んだのは、最後の定理
`wellFounded_step` が必要とするモジュールだけである。`expand` もその中にあり、そのファイルは
表記の定義の置き場所である `../Official.lean` にある。
`expand` を 474 個の入力で動かす `OmegaY/Official/Check.lean` は取り込んでいない。

wy-wo-por には、koteitan/1y-wo-por から取った 0-Y のモジュール `ZeroY/` と、BMS の層
`Por/BMS/` もある。これらはもう一度コピーはしない。同じモジュールを
[`../../Y/WellOrder/`](../../Y/WellOrder/README-ja.md) から import する（`ZeroY/` の
20 個と、`Por/BMS.lean` および `Por/BMS/` の 6 個）。

`expand` は、Naruyoko 氏のプログラム
[StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence)
（revision `b26ba7e`、既定の設定）の `expand` の規則に従う。wy-wo-por で規則の説明から
書いたもので、プログラムのコードは使っていない。プログラムにはライセンスが無い。

Apache-2.0 のファイルはヘッダをそのまま残す。ライセンスの本文は
[LICENSE-APACHE](../../../../LICENSE-APACHE)、出どころの記録は
[NOTICE](../../../../NOTICE) にある。

## 移植で変えたこと

* import のモジュール名に接頭辞 `Googology.Notation.OmegaY.WellOrder.` を付けた。
  `ZeroY.*` と `Por.BMS*` の import には、代わりに接頭辞
  `Googology.Notation.Y.WellOrder.` を付けた。
  `OmegaY/Official/Build.lean` は `../Official.lean` へ移した。それを import する
  ただ 1 つのファイル `OmegaY/Official/Reserve.lean` は、
  `Googology.Notation.OmegaY.Official` を import する。
* `Por/` の 3 個のファイルの名前空間 `Por` を `OmegaY.Por` に変えた。
  `../../Y/WellOrder/Por/` にある 1-Y のモデルが `Por` を使っていて、10 個の名前
  （`Por.R`、`Por.Sat`、`Por.Form` など）がぶつかるからである。モデルを使うファイルは
  名前空間 `OmegaY` の中にあるので、`Por.R` のような参照は、書き換えなくても
  `OmegaY.Por.R` を指す。コメントは `Por` のままである。
* どのファイルも `set_option backward.do.legacy false` を置く。Lean 4.33.1 は既定で
  新しい `do` のエラボレータを使い、Lean 4.30.0 は古い方を使う。この設定で Lean 4.30.0
  にも新しい方を使わせる。すると `expand` などのプログラムが wy-wo-por と同じ項になり、
  それを展開する証明が通る。
* どのファイルにも、移植したことを書いたヘッダの行がある。証明を変えたファイルは、
  何を変えたかを `Port change:` の行に書く。そういうファイルは 23 個あり、どれも
  `OmegaY/` の中にある。命題は一つも変えていない。変えかたは次の 5 種類である。
  * Lean 4.30.0 が `(fun x => …) a` の形を簡約せずに残すところで、タクティクの前に
    `beta_reduce` を置いた：`Expansion/Selection.lean`、
    `Official/Classification/Regions.lean`、`Official/Classification/Shape.lean`、
    `Official/Classification/Trace.lean`、
    `Official/Classification/Proofs/ChainCorrCopyMono.lean`、
    `Official/Classification/Proofs/StartRootPartsBlock0.lean`、
    `Official/Recon/FirstEmit.lean`、`Official/Recon/JumpLawAscend.lean`、
    `Official/Recon/LowerBndRows.lean`。
  * 両辺の違いが、添字 `xs[i]` の範囲の証明だけか、証明の中で書き直した `match` の
    matcher だけであるところで、`rw` を `erw` に替えるか、書き換えを項に替えた：
    `Official/Classification/Shape.lean`、`Official/Classification/KeyWitness.lean`、
    `Official/Classification/Proofs/ChainCorrStepInner.lean`、
    `Official/Classification/Proofs/CutPartsPaRow.lean`、
    `Official/Classification/Proofs/TopChainStart.lean`、
    `Official/Classification/Proofs/TSQCutRight.lean`、
    `Official/Recon/CrossPlainBlock0.lean`、`Official/Recon/CrossUpperNEnd.lean`、
    `Official/Recon/CrossUpperNStart.lean`、`Official/Recon/CrossUpperQ.lean`、
    `Official/Recon/CrossUpperWStart.lean`、`Official/Recon/LowerChainRecon.lean`。
  * `simp` が `M[x][1] = M[x][1]` を残すところで、後に `rfl` を置いた：
    `Official/Recon/PBStageBRootZero.lean`。
  * 前の `simp only` でもうゴールが閉じるところで、1 行を消した：
    `Official/Classification/Proofs/SeamStepUpper.lean`。
  * Mathlib v4.30.0 に無い `List.IsChain.rel_getLast_head_of_append` を
    `List.isChain_append` で置き換えた：`Official/Recon/RowLawColumn.lean`。

## 使う定理

```lean
-- ../Official.lean
def OmegaY.Official.expand (values : List Nat) (copies : Nat) : Result (List Nat)

-- OmegaY/Official/Descent.lean
def OmegaY.Official.Descent.Step (t s : List Nat) : Prop :=
  s ≠ [] ∧ ∃ n, Official.expand s n = .ok t

-- OmegaY/Official/Recon/FinalStageF.lean
theorem OmegaY.Official.Recon.FinalStageF.wellFounded_step : WellFounded Descent.Step
```

`Result` は `Except Error` である。`Descent.Step t s` は、$`s`$ が空でなく、ある
$`n`$ で $`t = s[n]`$ という意味である。$`s`$ にほかの条件は無い。自然数の列はどれも
状態である。同じファイルは `no_infinite_expansion` も証明する。どの $`k`$ でも
$`f(k+1) = f(k)[n_k]`$ となる列 $`f`$ は無い、という定理である。どちらも依存する公理は
`propext`、`Classical.choice`、`Quot.sound` だけである。
