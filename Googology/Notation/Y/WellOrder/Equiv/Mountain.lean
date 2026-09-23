/-
From koteitan, 1y-expand-equiv, `Equiv/Mountain.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.SibSucc
import Googology.Notation.Y.WellOrder.Equiv.RowSucc
import Googology.Notation.Y.WellOrder.OneY.NumericGeometry

open Googology.Notation.Y

/-!
# 鎖の根での段

JS が鎖の根に降りたとき、`firstAtLeast` が指す列は `root + 1` である。その値が
`c` の値以上であることを `root_step_le` で示す。

記号は次のとおり。行 `r` について

```
G = (rows base r).forest = frameAt s (r+1)   その行の森
F = frameAt s r                              frame（1 つ下の行の森、行 0 では線形森）
U = towerVal s r = (rows base r).value       frame の上の値
v = towerVal s (r+1) = (rows base (r+1)).value  次の行の値（= U の差分）
```

## 手順

```
1  root の G 子 p で c に至る道の上にあるものを取る（child_toward）
2  hreach から v c ≤ v p
3  root は G 子 p を持つので root+1 は生きている（rootChildAdjacent_tower）
4  root の F 子 e で p に至る道の上にあるものを取る
5  (1)  U p ≤ U (root+1)                     one_of_nonancestor_tower
6  (a)  root は root+1 の F 祖先              leftmost_child_all
7  v p ≤ v (root+1)                          diff_le_of_a_and_one
8  2 と 7 を繋いで v c ≤ v (root+1)
```
-/

namespace Yukito

open OneY OneY.Numeric

/-- 山の頂の高さは列番号以下。生きた列は 1 行ごとに右へずれるからである。 -/
theorem height_le_self' (base : Row) (hpos : ∀ c, 0 < base.value c) (c : Nat) :
    height base c ≤ c := by
  rcases Nat.lt_or_ge c (height base c) with h | h
  · have hl := height_live base (hpos c)
    rw [rows_value_zero_of_lt base _ c h] at hl
    omega
  · exact h

/-- `select (frameAt s r) (towerVal s r)` の差分は次の層の値そのもの。 -/
theorem difference_eq_towerVal (T : Tower) (r : Nat) :
    (select (frameAt T r) (towerVal T r)).difference = towerVal T (r + 1) := by
  funext c
  cases r with
  | zero =>
      show (match restrictedParent T.frame0 T.base.value c with
            | none => 0
            | some p => T.base.value c - T.base.value p) = _
      rw [← T.hbase c]
      rfl
  | succ k => rfl

/-- **鎖の根での段。** 歩行が根に到達したなら、`root + 1` は生きていて、その値は
`c` の値以上である。JS が根の所で `firstAtLeast` に指される列がこれである。 -/
theorem root_step_le (T : Tower) (r c root : Nat)
    (hanc : ZeroY.Forest.Ancestor (rows T.base r).forest.parent c root)
    (hreach : ∀ q, ZeroY.Forest.Ancestor (rows T.base r).forest.parent c q →
      (∃ t, (rows T.base r).forest.parent q = some t) →
      (rows T.base (r + 1)).value c ≤ (rows T.base (r + 1)).value q) :
    0 < (rows T.base (r + 1)).value (root + 1) ∧
      (rows T.base (r + 1)).value c ≤
        (rows T.base (r + 1)).value (root + 1) := by
  -- 手順 1
  obtain ⟨p, hGp, hpc⟩ := child_toward (ParentForest.ancestor_of_zeroY hanc)
  have hGp' : restrictedParent (frameAt T r) (towerVal T r) p = some root := by
    rw [← frameAt_step]; exact hGp
  -- 手順 2
  have h2 : (rows T.base (r + 1)).value c ≤
      (rows T.base (r + 1)).value p := by
    rcases hpc with ha | heq
    · exact hreach p (ParentForest.ancestor_to_zeroY ha) ⟨root, hGp⟩
    · rw [heq]
      exact Nat.le_refl _
  -- 手順 3
  obtain ⟨z, hz⟩ : ∃ z, (frameAt T (r + 1)).parent (root + 1) = some z := by
    rcases hq : (frameAt T (r + 1)).parent (root + 1) with _ | z
    · exact absurd (by rw [frameAt_step] at hq; exact hq)
        (rootChildAdjacent_tower T r root p hGp')
    · exact ⟨z, rfl⟩
  have hlive : 0 < (rows T.base (r + 1)).value (root + 1) :=
    (rows_parent_iff_next_live T.base r (root + 1)).mp ⟨z, hz⟩
  -- 手順 4
  obtain ⟨hancF, hposR, _, _⟩ :=
    (restrictedParent_some_iff (frameAt T r) (towerVal T r) p root).mp hGp'
  obtain ⟨e, hFe, hep⟩ := child_toward (ParentForest.ancestor_of_zeroY hancF)
  -- 手順 5
  have hone : towerVal T r p ≤ towerVal T r (root + 1) :=
    one_of_nonancestor_tower T r hGp hFe
      (by rcases hep with h | h
          · exact Or.inl (ParentForest.ancestor_to_zeroY h)
          · exact Or.inr h)
  -- 手順 6
  have hA : ZeroY.Forest.Ancestor (frameAt T r).parent (root + 1) root :=
    Relation.TransGen.single (leftmost_child_all T r root e hFe)
  -- 手順 7
  have h8 := diff_le_of_a_and_one (F := frameAt T r) (U := towerVal T r)
    root p (root + 1) hGp' hA hposR
    (fun _ h1 h2 => absurd h2 (by omega))
    ⟨z, by rw [← frameAt_step]; exact hz⟩ hone
  rw [difference_eq_towerVal] at h8
  have h8' : (rows T.base (r + 1)).value p ≤
      (rows T.base (r + 1)).value (root + 1) := h8
  exact ⟨hlive, by omega⟩

end Yukito
