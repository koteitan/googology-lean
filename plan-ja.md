[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画と現在地

このライブラリが何のためのもので、議論の全体がどういう形をしていて、作業が今
どこまで進んだかを書く。次の一手を選ぶ前に、まずここを見る。

## 何のためのライブラリか

巨大数の系——BMS、DBMS、Y 数列——は、行列や数列の上の書き換え系であり、問いは
「どの展開列も有限で止まるか」である。ライブラリはこれに標準的な方法で答える。
整列集合への測度で、一歩ごとに狭義に下がるものを見つける。

だから半分が 2 つと、その間の橋になる。

```
Notation/<系>/    系そのものと、順序数表記系
Trans/            それらの間の翻訳
Core/             共通の定理。測度 ⟹ 停止性
```

要点は、どの半分も**一度だけ**証明されることである。新しい系は 3 つのフィールドと
測度 1 つを出せばよく、残りは定理として受け取る。

## 1 つの系についての連鎖

後ろから読むと、作る順序になる。

```
BMS は停止する
  ⇐ Sim BMS ExBuchholz                    翻訳
  ⇐ WellFounded OTLt                      行き先が整礎
  ⇐ 標準形の主項が全部可到達
  ⇐ val が OT 上で狭義単調               表記系が正しい
  ⇐ ψ についての順序数の事実
```

最後の 2 つ以外は全部 `Core` が出す。最後の 2 つが、その表記系固有の数学である。

## 今どこまで来たか

### `Core/` — 完成

| ファイル | 中身 |
|---|---|
| `WF.lean` | `not_descending`、`not_wellFounded_of_descending` |
| `Rewrite.lean` | `Rewrite`、`Terminates`、`WF`、`terminates_of_wf`、`wf_of_measure`、`terminates_of_measure` |
| `Std.lean` | `Rewrite.Std`。標準形と生成元 |
| `Morphism.lean` | `OrdHom`、`Sim`、`StepHom`、`Equiv`、`Eval` と移送定理 |

`sorry` なし、外部依存なし。停止性だけが欲しいプロジェクトは、これだけ import
すればよい。

### `Notation/ExBuchholz/` — 試験台。作業中

| ファイル | 状態 |
|---|---|
| `Basic.lean` | 済。項、`cmp`、決定可能性 |
| `Order.lean` | 済。狭義線形順序と非狭義の順序 |
| `Std.lean` | 済。`G`、`isOT`、`OT`、決定可能 |
| `WF.lean` | 済。`not_wellFounded_lt`、`cmp_cons_cons'`、`OT` の構造補題、`OTLt` |
| `Sum.lean` | 済。主項の可到達性を仮定した `wellFounded_OTLt` |
| `Ord.lean` | 済。順序数の上の `ψ`、濃度評価、下方閉包性、加法的主要性 |
| `Eval.lean` | **作業中**。`val`、`Lam`、`val_mem_CSet`、`ψ` の比較補題 2 本 |

### `Trans/` — 空

### 他の系 — 未着手

## 残り 1 つ、詳しく

今は全部が次の 1 本に乗っている。

```
val は OT 上で狭義単調:  x < y → OT x → OT y → val x < val y
```

これが `OrdHom.wf` を通して `wellFounded_OTLt` の仮定を外す。

`ψ_v` の弱い単調性では足りない。`ψ_v(a) = ψ_v(a+1)` は実際に起きる。`a` が
`C_v(a)` の中に届かないときである。狭義にするのが標準形の条件の役目である。
4 段階ある。

| # | 段階 | 状態 |
|---|---|---|
| 1 | 閉包の元で十分小さいものは `ψ_v(a)` より下 | 済（`mem_CSet_of_le`、`lt_psi_of_mem`） |
| 2 | したがって `ψ_v(a)` は加法的主要 | 済（`isPrincipal_add_psi`） |
| 3a | **添字**は必ず自分の閉包の中にある | 済（`val_mem_CSet`、`val_lt_Lam` 経由） |
| 3b | **引数**も同様。ここで `G` を読む | **次** |
| 4 | 項の比較を値の比較に組み立てる | **次** |

### 3b と 4 が一緒になる理由

3b は 4 を要る。`G a (cons c d r)` は `a ≤ c` で場合分けし、もう一方の枝では
構文的に `c < a` が成り立っていて、証明には `val c < val a` が要る。それが 4 で
ある。逆に 4 も 3b を要る。2 つの主項が添字を共有する場合である。

だからこれは 1 つの同時帰納になる。測度は `size x + size y` で、どの呼び出しも
狭義に下がる。

* 4（`(cons a b t, cons c d u)`）は 4 を `(a,c)`、`(b,d)`、`(t,u)`、`(t, ψ_c(d))`
  で呼び、3b を `(a,b)` で呼ぶ
* 3b（`(a, cons c d r)`）は 3b を `(a,c)`、`(a,d)`、`(a,r)` で呼び、4 を `(c,a)`
  で呼ぶ

`Term.size` と比較補題 2 本（`psi_lt_of_sub_lt`、`psi_lt_of_arg_lt`）は入って
いる。残っているのは帰納そのものである。

## そのあと

1. `ExBuchholz` に基本列と `Rewrite` の値を与える
2. `G` と `isOT` を参照実装と較正する。今は Buchholz (1986) §2 の自然な拡張として
   書き下したもので、較正していない
3. `Notation/BMS` を足す
4. `Trans/BMS/ExBuchholz` を足す。ここで `Sim.terminates` から BMS の停止性が出る

## 約束ごと

* 主張は全部 Lean の定理であり、`sorry` も追加公理も無い
* `#guard` の行は小さい場合の計算であって定理ではない。見た目で分かるように分けて
  ある
* `Core` は mathlib を import しない。表記系が import するのは、順序数へ評価する
  ときだけである
