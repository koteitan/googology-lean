[← 戻る](../README-ja.md) | [English](TRIO-FIX-FUEL.md) | [Japanese](TRIO-FIX-FUEL-ja.md)

# Fix Fuel: 項とともに増える燃料

[koteitan/trio](https://github.com/koteitan/trio) の統合規則
([`TrioRulesAll.lean`](TrioRulesAll.lean)、Fix A–E と N) は、すべての再帰を 1 つの
固定の燃料 `TrioRules.fuel = 200` で回す。深さ 200 を超えると再帰が途中で止まり、
行列がまちがう。[`TrioTree.lean`](TrioTree.lean) は、異なる 2 つの標準項
`ψ_0(Ω + T_205)` と `ψ_0(Ω + T_206)` (`T_n` は `ψ_0` を `n` 重にしたもの、深さ 206 と 207)
が同じ行列になることを見つけた。

## パッチ

ファイル: [`TrioFixFuel.lean`](TrioFixFuel.lean) (パッチ本体)、
[`TrioFixFuelE0.lean`](TrioFixFuelE0.lean) (`ε₀` 未満の定理)、
[`TrioFixFuelSheet.lean`](TrioFixFuelSheet.lean) (チェック)。

* 規則は変えない。`fuel` を読む定義すべてに引数 `F` をつける
  (`TrioFixFuel.lean` の docstring の表)。中身は元の定義の `fuel` を `F` にしただけ。
* 標準形 `α` の燃料は `fuelOf α = max 200 (odDep α)`。`odDep` は入れ子の深さ。
  ビルダーは `MD α = MF (fuelOf α) α`。
* 項 `α` の燃料は `fuelT α = max 200 (tDep α)` (添字も数えた深さ)。読み取り `ofTerm` と
  ビルダーの両方に使う:
  `trioMatrixLD α = toRows (MF (fuelT α) (ofTerm (fuelT α) α))`。

## 証明したこと

* `MF_200 : MF 200 = MAll`: 燃料 200 では、コピーは元のプログラムと同じ。
* `MD_eq_MAll : odDep α ≤ 200 → MD α = MAll α`。項では
  `trioMatrixLD_eq : tDep α ≤ 200 → trioMatrixLD α = trioMatrixLAll α`。
  つまり深さ 200 までは何も変わらない。
* `ε₀` 未満では深さに関係なく `trioMatrixLD α = trioMatrix α`
  (`trioMatrixLD_eq_trioMatrix`)。よって
  `trioMatrixLD α < trioMatrixLD β ↔ α < β` で、`trioMatrixLD` は単射
  (`trioMatrixLD_lt_iff`, `trioMatrixLD_injective`)。
* `MstepAll_countable`: 可算な `α` (`lvlO F α = none`) では、統合規則の 1 ステップは
  規則 1–10 の 1 ステップに等しい。すべての `F` と `Mf` で成り立つ。
  `MstepAll_countable_200` は燃料 200 の場合で、`TrioRulesAll.lean` が「未証明」と
  書いている主張そのもの。

証明はシミュレーション。regime がないとき Fix B–D と N は働かないので、
Fix N 版のプログラム (`blockN`, `placeUnitsN`) は、内側の状態の上で素のプログラム
(`blockF`, `placeUnits`) と 1 ステップずつ同じに動く。

## チェックしたこと (`#guard`、証明ではない)

* [`TrioRulesAllSheet.lean`](TrioRulesAllSheet.lean) の 932 個の `#guard` すべてを、
  パッチ後の写像で同じ数値のまま通した: シートの行、順序チェック (783 個と 784 個の
  行列、不一致 0)、Fix A–E と N の guard、ステップの数 `(171, 0), (32, 6), (152, 7), (870, 257)`。
* 新しい `#guard` 23 個:
  * 使うラベルはすべて深さ `≤ 8`。そのすべてで、パッチ後の行列 = `TrioRulesAll` の行列。
  * どのラベルでも、燃料 `odDep α` だけで、燃料 `fuelOf α + 200` と同じ行列になる。
  * `ψ_0(Ω + T_205)` と `ψ_0(Ω + T_206)`: 古い写像は 1 つの行列、新しい写像は 2 つの行列を
    正しい順で出す。
  * `ψ_0(Ω + T_n)` で、新しい写像は深さ 191, 201, …, 301 で `TrioTree.trioE`
    (燃料なしの写像。順序を保つこと、標準形になることは証明ずみ) に等しい。
    古い写像が等しいのは深さ 200 まで。
  * この族の深さ 191–251: 行列は狭義に増える。
  * `ε₀` 未満の `ψ_0` の塔: 深さ 202, 210, 211, 260 で `trioMatrix` に等しい。古い写像は
    深さ 210 と 211 に同じ行列を出す。
  * 非可算の族 `ω^ω^…^(Ω+1)`、深さ 200–252: 深さ 201 で燃料 200 はレベル `Ω_1` を
    見つけられない (順序数を可算と読む)。深さ 203 から古い行列は順序が逆になる。
    新しい写像は深さ 197–209 で狭義に増える。深さ 201, 202, 252 で、燃料 `fuelOf α + 50`
    でも同じ行列になる。
* yaBMS (`bms -s`, `bms -c`、Lean の外): 深さ 200 付近の 3 つの族で、新しい行列は
  標準形で増える。非可算の族の古い行列は深さ 205 から標準形でなく、深さ 203 から順序が逆。

## まだ残っていること

* パッチ後の builder の下に、燃料 200 を読む箇所が 2 つ残る: `TrioRules.cmpAtomWith` の
  中の `lvl` と、`TrioRules.add` の中の `cmpExp`。どちらも入力の深さによらない。前者は
  atom にしか呼ばれず 1 ステップで止まる (定理 `lvl_atom`)。後者は定数 `ω + 1` と
  `Ω + 1` にしか呼ばれない。

* `ε₀` より上のすべての `α` で `fuelOf α` が足りること (燃料を増やしても変わらないこと)
  は証明していない。シートのラベルと上の族でチェックしただけ。
* `ε₀` より上の単射性は証明していない (燃料 200 でも証明されていない)。
  `TrioTreeRules.lean` の結果 (添字が 0 か 1 の項) は燃料 200 の `TrioRules` についての
  もので、パッチ後の統合写像には移していない。
* 計算: `Ω_{Ω_{…}}` のような深さ 150 の非可算の項は計算が終わらない
  (ビルダーが同じ引数で何度も自分を呼ぶ)。これはプログラムのコストで、燃料のせいではない。
