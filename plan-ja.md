[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画と現在地

このライブラリが何のためのもので、議論の全体がどういう形をしていて、作業が今
どこまで進んだかを書きます。次の一手を選ぶ前に、まずここを見ます。

## 何のためのライブラリか

巨大数の系——BMS、DBMS、Y 数列——は、行列や数列の上の書き換え系であり、問いは
「どの展開列も有限で止まるか」です。ライブラリはこれに標準的な方法で答えます。
整列集合への測度で、一歩ごとに狭義に下がるものを見つけます。

だから半分が 2 つと、その間の橋になります。

```
Notation/<系>/    系そのものと、順序数表記系
Trans/            それらの間の翻訳
Core/             共通の定理。測度 ⟹ 停止性
```

要点は、どの半分も**一度だけ**証明されることです。新しい系は 3 つのフィールドと
測度 1 つを出せばよく、残りは定理として受け取ります。

## 1 つの系についての連鎖

後ろから読むと、作る順序になります。

```
BMS は停止する
  ⇐ Sim BMS ExBuchholz                    翻訳
  ⇐ WellFounded OTLt                      行き先が整礎
  ⇐ 標準形の主項が全部可到達
  ⇐ val が OT 上で狭義単調               表記系が正しい
  ⇐ ψ についての順序数の事実
```

最後の 2 つ以外は全部 `Core` が出す。最後の 2 つが、その表記系固有の数学です。

## 今どこまで来たか

### `Core/` — 完成

| ファイル | 中身 |
|---|---|
| `WF.lean` | `not_descending`、`not_wellFounded_of_descending` |
| `Rewrite.lean` | `Rewrite`、`Terminates`、`WF`、`terminates_of_wf`、`wf_of_measure`、`terminates_of_measure` |
| `Std.lean` | `Rewrite.Std`。標準形と生成元 |
| `Morphism.lean` | `OrdHom`、`Sim`、`StepHom`、`Equiv`、`Eval` と移送定理 |

`Googology/Rank.lean` がその隣にあります。整礎な系は自前の順序数の測度——一歩の関係の
階数——を持つ、という定理です。mathlib が要るので `Core` には入れていません。

`sorry` なし、外部依存なし。停止性だけが欲しいプロジェクトは、これだけ import
すればよいです。

### `Notation/ExBuchholz/` — 試験台。作業中

| ファイル | 状態 |
|---|---|
| `Basic.lean` | 済。項、`cmp`、決定可能性 |
| `Order.lean` | 済。狭義線形順序と非狭義の順序 |
| `Std.lean` | 済。`G`、`isOT`、`OT`、決定可能 |
| `WF.lean` | 済。`not_wellFounded_lt`、`cmp_cons_cons'`、`OT` の構造補題、`OTLt` |
| `Sum.lean` | 済。主項の可到達性を仮定した `wellFounded_OTLt` |
| `Ord.lean` | 済。順序数の上の `ψ`、濃度評価、下方閉包性、加法的主要性 |
| `Eval.lean` | 済。`val`、`Lam`、`val_mem_CSet`、`ψ` の比較補題 2 本 |
| `Mono.lean` | 済。同時帰納、`val_lt_val`、`OTLt_wf` |
| `FS.lean` | 補題 1 本を除き済。`dom`、`fs`、`fs_lt`、`dom_eq_one_or_tw`、`step_lt`、`exb` |

**表記系としての `ExBuchholz` は完成した。**`OTLt_wf` が、標準形の上の順序が
仮定なしで整礎であることを言います。

### `Notation/BMS/` — 済

行数が任意のバシク行列。`bms_terminates r` がどの `r` でも成り立つ。
`r = 1, 2, 3` が原始数列・ペア数列・トリオ数列です。

停止性の証明そのものは
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern)——
`R_r` のラベルと Σ 初等部分構造による——で、このパッケージはそれを依存に持ちます。
`Notation/BMS/Basic.lean` が出すのは `Rewrite` の 3 フィールドと
`Subrelation.wf` 1 本だけで、残りは `Core` が出す。向こうの `Pat.StdR` が
こちらの `Rewrite.Rel` を手で書き下したものになっていたので、合わせ込みは
要りませんでした。

### `Trans/` — 空

### 他の系 — 未着手

## ExBuchholz の整礎性 — 済

```
val は OT 上で狭義単調:  x < y → OT x → OT y → val x < val y
```

が `OrdHom.wf` を通して `wellFounded_OTLt` の仮定を外した。無条件の形が
`OTLt_wf` です。

`ψ_v` の弱い単調性では足りません。`ψ_v(a) = ψ_v(a+1)` は実際に起きる。`a` が
`C_v(a)` の中に届かないときです。狭義にするのが標準形の条件の役目です。
4 段階あります。

| # | 段階 | 状態 |
|---|---|---|
| 1 | 閉包の元で十分小さいものは `ψ_v(a)` より下 | 済（`mem_CSet_of_le`、`lt_psi_of_mem`） |
| 2 | したがって `ψ_v(a)` は加法的主要 | 済（`isPrincipal_add_psi`） |
| 3a | **添字**は必ず自分の閉包の中にある | 済（`val_mem_CSet`、`val_lt_Lam` 経由） |
| 3b | **引数**も同様。ここで `G` を読む | 済（`val_mem_CSet_arg`） |
| 4 | 項の比較を値の比較に組み立てる | 済（`val_lt_val`） |

### 3b と 4 が一緒になった理由

3b には 4 が必要です。`G a (cons c d r)` は `a ≤ c` で場合分けしますが、もう一方の
枝では構文的に `c < a` が成り立っていて、証明に `val c < val a` が要ります。これが
4 そのものです。逆に 4 にも 3b が必要で、2 つの主項が添字を共有する場合がそれに
あたります。

だからこれは 1 つの同時帰納になります。測度は、単調性の側が `size x`、閉包の側が
`size a + size t` です。単調性の側で左の項だけを見るのは、`b` から `G` が集めた `z`
についての呼び出し `(z, b)` が、右の項では抑えられないからです。どの呼び出しも
狭義に下がります。

* 4（`(cons a b t, cons c d u)`）は 4 を `(a,c)`、`(b,d)`、`(t,u)`、`(t, ψ_c(d))`
  で呼び、3b を `(a,b)` で呼ぶ
* 3b（`(a, cons c d r)`）は 3b を `(a,c)`、`(a,d)`、`(a,r)` で呼び、4 を `(c,a)`
  で呼ぶ

それが `Mono.lean` です。

## 次

1. **`OT` と `· < Ω` が一歩の展開で保たれること。** Buchholz 補題 3.3 の拡張版で、
   ライブラリと `exb.WF` の間に残る唯一のものです。`test/ExBuchholzCheck.lean`
   で計算により確認済み。サイズ 8 以下の可算標準形 3835 個を `0`〜`4` のどれで展開
   しても標準形・可算・狭義減少が保たれる。サイズ 9（15890 個）でも同じ。ε₀、
   ψ_0(Ω+Ω)、ψ_0(ψ_1(1))、ψ_0(Ω_2)、ψ_0(ψ_Ω(0)) は途中の項が全部標準形のまま
   `0` に到達します。証明は `fs` の枝を
   1 つずつ追うもので、`G` の代入補題が必要になります
2. `Trans/BMS/ExBuchholz` を足します。BMS の停止性にはもう要らないので、翻訳が買うのは
   **値**です。行列がどの順序数を名指すか
4. DBMS と Y 数列を足す

## 約束ごと

* 主張は全部 Lean の定理で、`sorry` も追加公理もありません
* `#guard` の行は小さい場合の計算であって、定理ではありません。見た目で分かるように
  分けてあります
* `Core` は mathlib を import しません。表記系が import するのは、順序数へ評価する
  ときだけです
