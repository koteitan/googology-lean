[← Back](../../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# DBMS

DBMS の展開規則は BM4 と全く同じである。違うのは展開の出発点である。

BM4 の生成元は階段 `(0,…,0)(1,…,1)⋯(n,…,n)` である。DBMS の生成元は、列 `i` の
行 `k` に `i - k` を（`0` で打ち切って）置いた配列である。

```
(0,0,0)(1,0,0)(2,1,0)(3,2,1)⋯
```

## ここにあるもの

```lean
def dstair (r n : ℕ) : Arr r := ⟨n + 1, fun i k => i - k⟩

inductive DStd (r : ℕ) : Arr r → Prop
  | init (n : ℕ) : DStd r (dstair r n)
  | step {A : Arr r} (N : ℕ) : DStd r A → DStd r (expand A N)

noncomputable def dbms (r : ℕ) : Rewrite where
  State  := DStdElt r                 -- DBMS の生成元から到達可能な配列
  step   := fun A k => expand A k     -- BM4 と同じ規則
  halted := fun A => A.len = 0
```

二つの標準形は本当に違う。`(0,0)(1,1)` は BM4 の標準形だが DBMS の標準形では
なく、`(0,0)(1,0)(2,1)` は逆である。1 行のときは `i - 0 = i` なので一致する。

## 状態

| | |
|---|---|
| 展開系 | 済 |
| 生成元 | 済（`dbmsStd`） |
| 任意の行数での停止性 | **未証明** |
| 1 行での順序数と停止性 | 済。[`Trans/DBMS/`](../../Trans/README-ja.md) にある |

`r ≥ 2` の停止性はここでは証明していない。このライブラリが取り込んでいるラベル
系の証明は階段から到達可能な配列についてのものであり、この生成元に移るかどうかは
このリポジトリでは決着がついていない。

1 行は停止する。`Trans.DBMS.dbms_one_terminates` が拡張ブーフホルツ ψ への翻訳で
それを出し、`Trans.DBMS.dbmsOrdEval` が 1 行の各行列が名指す順序数を与える。
1 行では両系が一致するので、これは 1 行 BMS と同じ順序数である。
