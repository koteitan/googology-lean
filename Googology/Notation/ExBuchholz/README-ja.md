[← Back](../../../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# ExBuchholz

拡張ブーフホルツ psi。Maksudov による Buchholz の崩壊関数の拡張で、`ψ` の添字が
`ω` 以下の数ではなく、この系自身が名前を付けられる任意の順序数になる。

```
C_v^0(a)     = {b | b < Ω_v}
C_v^(n+1)(a) = {b + c, ψ_u(e) | u, b, c, e ∈ C_v^n(a) ∧ e < a}
C_v(a)       = ⋃_{n<ω} C_v^n(a)
ψ_v(a)       = min {g | g ∉ C_v(a)}
```

`Ω_0 = 1`、`v > 0` では `Ω_v` は濃度 `ℵ_v` の最小の順序数。可算な極限は `p0(Λ)`
で、`Λ` は最初の omega 不動点である。

## 項の型

再帰引数 3 つの単一の帰納型。相互帰納も入れ子帰納も使わないので、以下の再帰は
全部構造帰納である。

```lean
inductive Term where
  | nil  : Term                       -- 0
  | cons : Term → Term → Term → Term  -- ψ_a(b) + t
```

項は主項 `ψ_a(b)` の有限和である。添字が項であることが、この拡張の中身そのもので
ある。

## ファイル

| ファイル | 中身 |
|---|---|
| `Basic.lean` | `Term`、`cmp`、`lt`、`le`、決定可能性、`cmp_self`、`cmp_swap`、`cmp_eq_iff` |
| `Order.lean` | `lt_irrefl`、`lt_trans`、`lt_trichotomy`、`lt_asymm` |
| `Std.lean` | `G`、`isOT`、`OT`、決定可能性 |

## 順序

`cmp` は主項のリストの辞書式順序で、真の前半が小さい方になる。主項どうしは
`(添字, 引数)` の辞書式で比べる。Buchholz の `(<1)`–`(<3)` で、添字を数から項に
一般化したものである。

`Order.lean` はこれが狭義の線形順序であることを証明する。この 3 つは
`Googology.Core.Morphism` の `OrdHom.injective` が要求するものそのものなので、
この系への翻訳は順序を保つだけで単射になる。

## 標準形

`ψ_a(b)` が標準形であるとは、`ψ_a` がまだ届く `b` の部分項が全部 `b` より真に
小さいことをいう。和が標準形であるとは、主項が広義単調減少であることをいう。
集める関数 `G` は Buchholz のものだが、内側の `ψ_c(d)` の添字 `c` 自身が項なので、
`d` と一緒に `c` も集める点が違う。

`isOT` は `Bool` を返す決定手続きなので、小さい場合は `#guard` が計算で確かめる。
`Std.lean` に入れたものには、`ε₀ = ψ_0(Ω)` が標準形であること、`1 + ω` は主項が
増えるので標準形でないこと、`ψ_0(ψ_0(Ω))` は `Ω` が引数より下にないので標準形で
ないことが含まれる。

## 状態

| | |
|---|---|
| 項の型、順序、決定可能性 | 済 |
| 狭義線形順序 | 済 |
| `G`、標準形、決定可能性 | 済 |
| 整礎性 | **未** |
| 基本列、`Rewrite` の値 | **未** |
| 順序数への評価 | **未** |

例外的に `sorry` を許しているわけではない。ファイルに `sorry` も `axiom` も無い。

### 出典のあるもの・無いもの

上の `ψ` の定義は Maksudov のもので、Googology Wiki に載っている。それに対応する
表記系は p進大好きbot による。ここに書いた `G` と標準形の条項は、Buchholz (1986)
§2 の自然な拡張として書き下したもので、参照実装との**較正はしていない**。今のところ
証拠は `#guard` の行だけで、小さい項を数個しか覆っていない。順序は確定、標準形の
述語は暫定、として扱うこと。較正ファイルができるまでは変わりうる。

## 名前について

`EBuchholz` でも `EBP` でもなく `ExBuchholz` にした。mathlib は「拡張した X」を
`E` の接頭辞で綴る——`ENat`、`EReal`、`ENNReal`、`EMetricSpace`——が、その読み方は
人名の前では壊れる。`EBuchholz` はイニシャル「E. Buchholz」と見分けがつかない。
`Ex` なら「拡張」以外には読めない。

## 出典のあるもの・無いもの

上の `ψ` の定義は Maksudov のもので、Googology Wiki に載っている。それに対応する
表記系は p進大好きbot による。ここに書いた `G` と標準形の条項は、Buchholz (1986)
§2 の自然な拡張として書き下したもので、参照実装との**較正はしていない**。今のところ
証拠は `#guard` の行だけで、小さい項を数個しか覆っていない。順序は確定、標準形の
述語は暫定、として扱うこと。較正ファイルができるまでは変わりうる。

## 名前について

`EBP` ではなく `ExBuchholz` にした。mathlib は「拡張した X」を頭字語ではなく名前の
方に `E` を付けて綴る——`ENat`、`EReal`、`ENNReal`、`EMetricSpace`。`EBP` が
よければ 1 行の変更で済む。

## 出典

- Extended Buchholz's function, Googology Wiki.
  https://googology.miraheze.org/wiki/Extended_Buchholz%27s_function
- W. Buchholz, A new system of proof-theoretic ordinal functions,
  Annals of Pure and Applied Logic 32 (1986) 195–207.
