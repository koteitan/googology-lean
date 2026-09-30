[English](TRIO-FIX-STRIP.md) | [Japanese](TRIO-FIX-STRIP-ja.md)

# パッチ "strip": 先頭がアトムでない指数での規則 1

ファイル: [TrioFixStrip.lean](TrioFixStrip.lean) (パッチ),
[TrioFixStripSheet.lean](TrioFixStripSheet.lean) (検査: 要約と最初の一部。残りは
`TrioFixStripSheet1b`–`1h`, `TrioFixStripSheet2`, `TrioFixStripSheet9`,
`TrioFixStripSheet9Frag7`, `TrioFixStripSheet9Wide`。それぞれ数分で検査できるように分けた),
[TrioFixStripTree.lean](TrioFixStripTree.lean) (断片での順序と標準形)。
パッチは [TrioFixOfTerm.lean](TrioFixOfTerm.lean) (読み方 `ofTermFix`) と
`TrioRulesAll` (規則 1–10 と Fix A–E, N) の上にのる。

## 問題

読み方 `ofTermFix` にすると、`TrioTree` の順序の定理が成り立たなくなった
(`TrioFixOfTerm.not_trioMatrixLFix_lt_iff`):

    α = ψ_0(ψ_1(ψ_0(Ω)))              = ε_{ε₀}
    β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))   = ε_{ε₀^{ε₀^ω}}
    α < β なのに M(β) < M(α)

ビルダーは項 ω^δ を 1 つの列にし、その子に `strip δ` を書く。
これは ω^δ = ψ_v(Y) となる引数 Y のこと。`strip` は δ = h·c + ρ の先頭 h·c を見る:

| 先頭 h | 子 | 理由 |
|---|---|---|
| ψ_v(X) | X + ψ_v(X)·(c-1) + ρ | ω^δ = ψ_v(X + …) |
| Ω_v | Ω_v·(c-1) + ρ | ω^δ = ψ_v(Ω_v·(c-1) + ρ) |
| ω^e (アトムでない) | δ | δ の先頭指数の鎖が 0 か Ω_v で終わるときだけ正しい |

β の指数は ω^(ε₀·ω) = ψ_0(Ω + ψ_0(Ω+1)) で、ε₀·ω = ω^(ε₀+1) の先頭は ω^(ε₀+1)。
その鎖はアトム ε₀ = ψ_0(Ω) で終わる。`strip` は ε₀·ω を返していた。これは
ψ_0(ψ_0(Ω+1)) の木 (標準形でない項。ブーフホルツの体系では ε₀ と同じ)。
正しくは Ω + ε₀·ω、つまり ψ_0(Ω + ψ_0(Ω+1)) の木。

## 変更

`chainAtom h`: h の先頭指数をたどって、アトム (または 0) に着くまで進む。

- `stripSt δ`: 表の 1, 2 行目はそのまま。3 行目で `chainAtom h = ψ_v(X)` なら、子は
  **X + δ** (ψ_v(X + δ) = ω^(ψ_v(X) + δ) = ω^δ)。そうでなければ前と同じ δ。
- `headIsPsi (ato e)` のかわりに `uncollapses e` (子の `arg` フラグ):
  先頭の `chainAtom` が ψ アトムなら true。先頭がアトムなら前と同じ。
  新しい場合も true。子はやはり引数 X から始まるから。

マージのために: `TrioRules.strip` の本体を `stripSt` に、`headIsPsi (ato e)` を
`uncollapses e` に置き換える (`blockF`, `blockF2`, `blockN` と、ほかのパッチのコピーで)。
それ以外は変えない。パッチは `tailBlockF`, `tailBlock`, `unitTailLevel`, `tailLevel`,
`blockN`, `restate`, `placeUnitsN`, `finishN`, `MstepAll` を、この 2 つの置き換えだけで
コピーしている。
`stripSt_eq_strip`, `uncollapses_eq`: 先頭がアトムでなく、その鎖が ψ アトムで終わるとき以外は
新旧の規則は同じ。ε₀ より下には ψ アトムがないので、そこでは何も変わらない。

Lean で証明したこと: `trioMatrixLSt_tβ` (β は項の木になる)、`trioMatrixLSt_tα_lt_tβ`
(M(α) < M(β))。

## 検査 (`TrioFixStripSheet*.lean`, すべて `#guard`, 全部で 968 個)

| 検査 | パッチ後 (`trioMatrixLSt`) | 前 (`trioMatrixLFix`) |
|---|---|---|
| `TrioRulesAllSheet.lean` の全 guard (シートの行、783 / 784 の順序、Fix A–E, N、相互作用、1 ステップ比較) | すべて成立 | すべて成立 |
| コーパス (1,225 ラベル) で変わったラベル | 0 | – |
| シートに行がある 42 項: 行列 = シート、784 との不一致 | 42, 0 | 42, 0 |
| (ε₀·ω)[n] = ε₀·(n+1), n = 0..3 | はい | はい |
| smallFrag 6 (610): 不一致, 衝突 | 0, 0 | 0, 0 |
| ψ ≤ 7 個, 添字 0/1 (2,397): 不一致, 衝突 | **0, 0** | 127, 0 |
| その族で行列が変わった項 | β だけ | – |
| 添字 0,1,2 (491) | 75, 8 | 75, 8 |
| α < Ω_2, 添字 0,1 (524) | 0, 0 | 0, 0 |
| α < Ω_Ω, 添字 0,1,ω (537) | 63, 11 | 63, 11 |
| α < Ω_{Ω_Ω}, 添字 0,1,Ω (537) | 137, 29 | 137, 29 |

広い 4 つの族では、パッチはどの行列も変えない。なのでそこでの失敗は、ビルダーの別の欠陥。

標準形 (yaBMS `bms -s`, Lean の外): ψ ≤ 7 個の族の 2,397 行列はすべて標準形
(前は β 以外すべて)。広い族は前と同じ: 添字 0,1,2: 異なる 483 個のうち 2 個が標準形でない、
α < Ω_2: 524 個中 0、0,1,ω: 527 個中 30、0,1,Ω: 512 個中 59。

## 断片での順序と標準形 (`TrioFixStripTree.lean`)

`trioE2` はパッチ後の写像を構造的再帰で書いたもの (`TrioTree.trioE` と同じやり方)。
変わるのは加法単位 ψ_0(b) の桁だけ。b = h + l (h = ψ_1 の項、
l = ψ_0 の項 ψ_0(g_1) + ψ_0(g_2) + …) とすると:

    ψ_0(b) = ω^(ψ_0(h) + l)
    桁: ψ_0(h) (h < g_1 なら落とす。そのとき ψ_0(h) + l = l)、次に ψ_0(g_j) ごとに 1 桁
    ψ_0(g) の桁は expoT(g) の木。ψ_0(g) = ω^expoT(g):
      expoT(g) = g                    (g に Ω がないとき)
               = ψ_0(hi g) + lo g     (それ以外。hi g < lo g の最初の引数なら lo g だけ)

(前の写像は 1 桁で、ψ_0(b) の木だった。)

証明したこと。標準形 α, β < Ω で、添字がすべて 0 か 1 のとき:

- `trioE2_lt_iff`: trioE2 α < trioE2 β ↔ α < β。`trioE2_injective`。
- `trioE2_std`: trioE2 α は 3 行 BMS の標準形。

主な段階: `expoT_lt` (出てくる引数の上で expoT は順序を保つ)、`good_of_OT`、
`OT_psi_hiPart` (ψ_0 の標準的な引数の Ω 部分に ψ_0 をつけても標準形)、
`TrioTreeStd.reach_units`。

## まだ正しくないこと / 証明していないこと

1. **プログラムが `trioE2` を計算することは証明していない。** `trioMatrixLSt α = trioE2 α` は
   `smallFrag 7` の 2,398 項で検査し (`#guard`)、上の α, β では証明した。前の証明
   `TrioTreeRules.trioMatrixL_eq_trioE` は規則 1–10 と `ofTerm` についてのもの。新しい証明には、
   合併ビルダー (Fix A–E, N) と `ofTermFix`, `stripSt` が要る (新しい指数でのプログラムの比較、
   `add` での吸収、レジームなしの `placeUnitsN` のシミュレーション)。なので `trioMatrixLSt`
   そのものの順序と標準形の定理は、この検査に頼っている。これを未解決の `Prop` `CalibSt`
   (∀ α, OT α → α < Ω → Sub01 α → trioMatrixLSt α = trioE2 α) として書き、
   `trioMatrixLSt_lt_iff_of_calib`, `trioMatrixLSt_std_of_calib` をそこから証明した。
2. **大きい添字。** 添字 0,1,2 / 0,1,ω / 0,1,Ω での失敗は変わらない (不一致 75 / 63 / 137)。
   これは別の欠陥で、今回のものではない。
