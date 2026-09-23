/-
From koteitan, 1y-expand-equiv, `Equiv/Sparse.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below; the import of `OneY.Extraction` that `Equiv/Yukito.lean` carried is made here).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.Yukito
import Googology.Notation.Y.WellOrder.OneY.Extraction

open Googology.Notation.Y

/-!
# 疎配列の走査

JS は行を「生きたセルだけを `position` 昇順に並べた配列」で持つ。列番号で引くには
`while (row[j].position < target) j++` で走査する。本ファイルはこの走査
（`scanFrom` / `firstAtLeast`）の性質を証明する。

要点は 3 つである。

```
firstAtLeast_before  それより手前のセルは position が target 未満
firstAtLeast_at      止まった所のセルは position が target 以上
firstAtLeast_eq_of_mem  position がちょうど target のセルがあれば、そこで止まる
```

3 つ目が「疎配列を列番号で引く」の正しさである。逆に、ちょうどのセルが無いと
`firstAtLeast` は**右隣のセルを指す**。これが山の段で唯一の食い違いになる箇所で、
`Mountain.lean` の `root_step_le` がそこを埋める。
-/

namespace Yukito

/-- 位置が狭義単調増加であること。JS の行はつねにこの形をしている。 -/
def PosMono (row : Rowj) : Prop :=
  ∀ i j, (hi : i < row.size) → (hj : j < row.size) → i < j →
    (row[i]'hi).pos < (row[j]'hj).pos

/-- 止まる手前のセルは `position` が `target` 未満。 -/
theorem scanFrom_before (row : Rowj) (target : Nat) :
    ∀ j i, ∀ hi : i < row.size, j ≤ i → i < scanFrom row target j →
      (row[i]'hi).pos < target := by
  intro j
  induction j using scanFrom.induct row target with
  | case1 j h hlt ih =>
      intro i hi hji hlt2
      rw [scanFrom.eq_def row target j, dif_pos h, if_pos hlt] at hlt2
      rcases Nat.eq_or_lt_of_le hji with heq | hgt
      · subst heq; exact hlt
      · exact ih i hi hgt hlt2
  | case2 j h hge =>
      intro i hi hji hlt2
      rw [scanFrom.eq_def row target j, dif_pos h, if_neg hge] at hlt2
      omega
  | case3 j h =>
      intro i hi hji hlt2
      rw [scanFrom.eq_def row target j, dif_neg h] at hlt2
      omega

/-- 止まった所のセルは `position` が `target` 以上。 -/
theorem scanFrom_at (row : Rowj) (target : Nat) :
    ∀ j k, ∀ hk : k < row.size, scanFrom row target j = k →
      target ≤ (row[k]'hk).pos := by
  intro j
  induction j using scanFrom.induct row target with
  | case1 j h hlt ih =>
      intro k hk he
      rw [scanFrom.eq_def row target j, dif_pos h, if_pos hlt] at he
      exact ih k hk he
  | case2 j h hge =>
      intro k hk he
      rw [scanFrom.eq_def row target j, dif_pos h, if_neg hge] at he
      subst he
      omega
  | case3 j h =>
      intro k hk he
      rw [scanFrom.eq_def row target j, dif_neg h] at he
      omega

theorem firstAtLeast_before (row : Rowj) (target i : Nat) (hi : i < row.size)
    (h : i < firstAtLeast row target) : (row[i]'hi).pos < target :=
  scanFrom_before row target 0 i hi (Nat.zero_le _) h

theorem firstAtLeast_at (row : Rowj) (target k : Nat) (hk : k < row.size)
    (h : firstAtLeast row target = k) : target ≤ (row[k]'hk).pos :=
  scanFrom_at row target 0 k hk h

/-- **走査の特徴づけ。** 添字 `j` の位置が `target` 以上で、それより手前がすべて
`target` 未満なら、`firstAtLeast` は `j` を指す。 -/
theorem firstAtLeast_eq (row : Rowj) (target j : Nat) (hj : j < row.size)
    (h1 : target ≤ (row[j]'hj).pos)
    (h2 : ∀ i, ∀ hi : i < row.size, i < j → (row[i]'hi).pos < target) :
    firstAtLeast row target = j := by
  rcases Nat.lt_trichotomy (firstAtLeast row target) j with hlt | heq | hgt
  · exfalso
    have hk : firstAtLeast row target < row.size := by omega
    have hge := firstAtLeast_at row target _ hk rfl
    have := h2 _ hk hlt
    omega
  · exact heq
  · exfalso
    have := firstAtLeast_before row target j hj hgt
    omega

/-- **疎配列を列番号で引く。** 位置が狭義単調で、`position` がちょうど `target` の
セルがあれば、`firstAtLeast` はそのセルを指す。 -/
theorem firstAtLeast_eq_of_mem (row : Rowj) (hmono : PosMono row) (target m : Nat)
    (hm : m < row.size) (hpos : (row[m]'hm).pos = target) :
    firstAtLeast row target = m :=
  firstAtLeast_eq row target m hm (by omega)
    (fun i hi hlt => by have := hmono i m hi hm hlt; omega)

end Yukito
