/-
From koteitan, 1y-expand-equiv, `Equiv/RowSucc.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Row0
import Googology.Notation.Y.WellOrder.OneY.NumericGeometry

open Googology.Notation.Y

/-!
# 行 `r+1` の親：正値条件は「鎖の根を除く」ことと同じ

Lean 側の行 `r+1` の親は

```
(rows base (r+1)).forest.parent c
  = restrictedParent (rows base r).forest (rows base r).difference c
  = greatestBelow? c (fun p => p が行 r の森で c の祖先
                             ∧ 0 < 差分 p ∧ 差分 p < 差分 c)
```

である。JS 側は行 `r` の親チェーンを辿って最初に値の小さいものを取るだけで、
正値条件に当たるものを持たない。両者が食い違わない理由は次の一点にある。

> 行 `r` で親を持つ列は、行 `r+1` で必ず値が正になる。

したがって祖先鎖 `c > p₁ > p₂ > … > p_last` のうち、行 `r+1` で死んでいるのは
鎖の根 `p_last` だけであり、正値条件はちょうどその根だけを落とす。
本ファイルはこれを示す。
-/

namespace Yukito

open OneY.Numeric

/-- 行 0 の証明の最終段は `r` に依らない。親の値についての 2 つの不等式から、
差分についての不等式が出る。

`v p = U p - U root`、`v j = U j - U t` であり、`U t ≤ U root` と `U p ≤ U j`
から `v p ≤ v j` が従う。 -/
theorem difference_le_of_value_le (a : Row) {p root j t : Nat}
    (hp : a.forest.parent p = some root)
    (ht : a.forest.parent j = some t)
    (hUt : a.value t ≤ a.value root)
    (hUpj : a.value p ≤ a.value j) :
    a.difference p ≤ a.difference j := by
  have h1 : a.difference p = a.value p - a.value root := by
    simp only [Row.difference, hp]
  have h2 : a.difference j = a.value j - a.value t := by
    simp only [Row.difference, ht]
  omega

/-! ## 密表現側：行 `r` では列 `r` 未満は死んでいる -/

/-- 行 `r` では列 `r` 未満の値は 0。列 `c` が行 `r+1` で生きるにはその親が行 `r` で
生きていなければならず、親は左にあるから、生きた列は 1 行ごとに右へ 1 つ以上ずれる。 -/
theorem rows_value_zero_of_lt (base : Row) :
    ∀ r c, c < r → (rows base r).value c = 0 := by
  intro r
  induction r with
  | zero => intro c h; exact absurd h (Nat.not_lt_zero c)
  | succ r ih =>
      intro c hc
      show (rows base r).difference c = 0
      cases hp : (rows base r).forest.parent c with
      | none => simp only [Row.difference, hp]
      | some p =>
          exfalso
          have hpv := ((rows base r).parent_values hp).1
          have hlt := (rows base r).forest.parent_left hp
          rw [ih p (by omega)] at hpv
          omega

/-- 入力列の外の列は値 1 である。`ofSequence` がそう定めている。 -/
theorem ofSequence_value_ge (s : List Nat) (c : Nat) (h : s.length ≤ c) :
    (ofSequence s).value c = 1 := by
  show s[c]?.getD 1 = 1
  rw [List.getElem?_eq_none h]
  rfl

end Yukito
