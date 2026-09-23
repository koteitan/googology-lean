[← Back](../README.md) | [English](TRIO-FIX-MUL-NORMALIZE.md) | [Japanese](TRIO-FIX-MUL-NORMALIZE-ja.md)

# パッチ: `mul` と `power` で `ω^atom = atom` にする

[`TrioRulesAll.lean`](TrioRulesAll.lean) の上に置く、独立したパッチです。`TrioRulesAll.lean` は
[koteitan/trio](https://github.com/koteitan/trio) の規則 1–10 に、修正 A–E と N を入れたものです。
コードは [`TrioFixMulNormalize.lean`](TrioFixMulNormalize.lean) にあります。
検査は [`TrioFixMulNormalizeSheet.lean`](TrioFixMulNormalizeSheet.lean) にあります。

## 不具合

これは [TRIO-SHEET-41-ja.md](TRIO-SHEET-41-ja.md) の副次的な発見です。`mul` は、`ω^3·Ω` の指数
`ω^(3+Ω)` を `.o [(.W 1, 1)]` と書きます。これは正規形 `Ω` を指数として包んだものです。正しくは原子
`.W 1` です。二つは同じ順序数で、`cmp_ord` も `Ω_{ω^3·Ω} = Ω_Ω` と判定します。しかし、ビルダーは形を
読みます。`Ω_{ω^3·Ω}` はレベル `ω^Ω` として `placeUnits` に回し、`Ω_Ω` は規則 2 に回します。そのため、
行 4369 の印字ラベル `W_(w^3*W)` には、`W_W` と違う行列が付きます。`power` にも同じ不具合があります。
`ω^Ω` を `ω^(ω^Ω)` と書きます。

## 変更

1. `x` が原子（`Ω_v` か `ψ_v(X)`）のとき、`mkExp [(x, 1)] = x` とします。それ以外は
   `mkExp a = .o a` です。
2. `mulM`: `mul` の `.o (addExp e1 e)` を `mkExp (addExp e1 e)` に替えたものです。
3. `powerM`: `power` の `mul` を `mulM` に、`wpow b` を `wpowM b = [(mkExp b, 1)]` に替えたものです。
4. `parseM`: ラベルの読み取りで、`mulM` と `powerM` を使うようにしたものです。規則のほかの部分は
   `mul` も `power` も呼びません。
5. `MstepFix`: `MstepAll` の判定 `alpha == [(.W v, 1)]` を、パターン `alpha = [(.W _, 1)]` に替えたもの
   です。計算結果は変わりません。

2 と 3 では、`== .o []` と `== one` もパターンマッチに替えます。`Ex` の導出 `==` は、証明の中で簡約され
ません。`Ex.W v == Ex.o []` さえ簡約されません。そのため、2、3、5 はパターンで書きます。

次のことを証明しました: `ato (mkExp a) = a`、`mkExp` が `.o [(atom, 1)]` を作らないこと、
`mulM (ω^3) Ω = Ω`、`powerM ω Ω = Ω`、`MstepFix Mf Ω_w = MOmega2 Mf w`（すべての `w` で規則 2）、
可算な `α` と `ψ_{Ω_u}(X)` で `MstepFix = MstepAll` となること。`mulM` と `mul` を比べる定理は作れません。
`mul` が導出 `==` を使うからです。代わりにガードで確かめます。

## 検査

| 検査 | 結果 |
|---|---|
| `TrioRulesAllSheet.lean` のガード（Part 1–7） | 意図した 1 か所の変化を除き、すべて成立 |
| 読み取りが変わるラベル（重複なし） | 1,209 個中 1 個: 行 4369 の印字ラベル |
| 行列が変わるラベル（重複なし） | 同じ 1 個だけ。`M(Ω_Ω)` になる |
| `parseM` の出力が正規形 | 1,209 / 1,209（`parse` では 1,208） |
| 順序検査、785 ラベル（印字ラベル 2 個を含む） | 不一致 0（パッチなしでは 1） |
| Part 7 の件数（1 ステップを規則 1–10 と比較） | 変化なし: 171/0, 32/6, 152/7, 870/257 |
| `ω^atom` を含む手作りラベル 22 個 | パッチ後の行列は正規形の行列と同じ。すべて標準形（yaBMS `bms -s`）。選んだ 784 行列との順序不一致は 0 |
| 同じ 22 個、パッチなし | 17 個が正規形の行列と違う。5 個が非標準。順序不一致は 62 |

行 4369 の訂正ラベル `Ω_{ω^3}·Ω` の行列は変わりません。

## 残っていること

- Python の参照プログラム [`tools/probe_eps_range.py`](https://github.com/koteitan/trio/blob/main/tools/probe_eps_range.py)
  にも、同じ `mul` と `power` があります。両者を同じに保つため、こちらにも同じスマートコンストラクタが
  必要です。
- ビルダー自体は、今も入力の形を読みます。ほかの経路で `.o [(atom, 1)]` が作られると、やはり誤って
  扱います。このパッチの後、順序数を作るのはラベルの読み取りだけです。1,209 個のラベルすべてで、その
  出力は正規形です（ガードで確認）。
