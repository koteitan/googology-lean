/-
From koteitan, 1y-expand-equiv, `Equiv/Row0.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below; the import of `OneY.Extraction` that `Equiv/Yukito.lean` carried is made here), and `YesMetaZFC.BMS` by `Por.BMS`;
the proof of `scanLeft_eq_greatestBelow` unfolds `greatestBelow?` through `greatestBelow?_succ`,
since `Por.BMS.greatestBelow?` is not defined by recursion.
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.Yukito
import Googology.Notation.Y.WellOrder.OneY.Extraction
import Googology.Notation.Y.WellOrder.ZeroY.Forest.MatrixParents
import Googology.Notation.Y.WellOrder.ZeroY.Forest.Comparison

open Googology.Notation.Y

/-!
# 行 0 の親探索の一致

JS `calcMountain` の行 0 は

```js
p = position+1;
while (true){ p--; j = p-1; if (j<0) break;
              if (lastLayer[j].value < lastLayer[i].value){ parentIndex = j; break; } }
```

で `j = c-1, c-2, …, 0` と左へ走り、最初に値が小さいものを親にする。
Lean 側は `restrictedParent linearForest v c`、すなわち
`greatestBelow? c (fun p => p が c の祖先 ∧ 0 < v p ∧ v p < v c)` である。

行 0 の frame は `linearForest`（親は `c-1`）なので祖先条件は `p < c` と同値であり、
両者は同じ関数になる。本ファイルはそれを示す。
-/

namespace Yukito

open OneY.Numeric Por.BMS

/-- JS の左スキャンを値関数の形で書いたもの。`j` から下へ走る。 -/
def scanLeft (v : Nat → Nat) (target : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if v j < target then some j else scanLeft v target j

/-- 左スキャンは `greatestBelow?` そのものである。定義が同じ形なので帰納法で済む。 -/
theorem scanLeft_eq_greatestBelow (v : Nat → Nat) (target : Nat) :
    ∀ j, scanLeft v target j = greatestBelow? j (fun k => decide (v k < target))
  | 0 => rfl
  | j+1 => by
      rw [greatestBelow?_succ]
      simp only [scanLeft]
      by_cases h : v j < target
      · simp [h]
      · simp [h, scanLeft_eq_greatestBelow v target j]

/-- 行 0 の frame は線形森なので、祖先条件は `p < c` と同値である。 -/
theorem linear_ancestorChain_contains (c p : Nat) (hp : p < c) :
    (ancestorChain ZeroY.linearParent c c).contains p = true :=
  (ZeroY.Forest.ancestorChain_contains_iff ZeroY.linearParent_leftward).mpr
    (ZeroY.linearParent_ancestor_of_lt hp)

/-- 値がすべて正なら、行 0 の `restrictedParent` は左スキャンに一致する。
祖先条件は `greatestBelow?` の探索範囲 `p < c` に含まれ、正値条件は仮定から常に真。 -/
theorem restrictedParent_linear (v : Nat → Nat) (hv : ∀ p, 0 < v p) (c : Nat) :
    restrictedParent linearForest v c = scanLeft v (v c) c := by
  rw [scanLeft_eq_greatestBelow]
  unfold restrictedParent
  apply ZeroY.Forest.greatestBelow?_congr
  intro p hp
  simp only [linearForest, linear_ancestorChain_contains c p hp, Bool.true_and]
  simp [hv p]

end Yukito
