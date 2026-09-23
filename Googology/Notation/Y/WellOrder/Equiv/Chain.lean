/-
From koteitan, 1y-expand-equiv, `Equiv/Chain.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.OneY.ForestBridge


/-!
# 親鎖についての小補題

`ParentForest.Ancestor` の鎖を 1 歩ずつ扱うための道具。どれも森の形だけを使う。
-/

namespace Yukito

open OneY

/-- 祖先を持つ列は親を持つ。 -/
theorem ancestor_parent_exists' {F : ParentForest} {a c : Nat}
    (ha : F.Ancestor a c) : ∃ q, F.parent c = some q := by
  cases ha with
  | direct hp => exact ⟨_, hp⟩
  | step _ hp => exact ⟨_, hp⟩

/-- 鎖の分解。`c` の祖先は、親 `q` そのものか、`q` の祖先である。 -/
theorem ancestor_cases {F : ParentForest} {a c q : Nat}
    (hq : F.parent c = some q) (ha : F.Ancestor a c) : a = q ∨ F.Ancestor a q := by
  cases ha with
  | direct hp =>
      rw [hq] at hp
      injection hp with h
      exact Or.inl h.symm
  | step h hp =>
      rw [hq] at hp
      injection hp with he
      subst he
      exact Or.inr h

/-- 親は最も右の祖先。 -/
theorem ancestor_le_of_parent {F : ParentForest} {a c q : Nat}
    (hq : F.parent c = some q) (ha : F.Ancestor a c) : a ≤ q := by
  rcases ancestor_cases hq ha with he | h
  · omega
  · exact Nat.le_of_lt h.lt

/-- 鎖を反対の端から見る。`root` が `e` の祖先なら、`root` の子で
`e` へ至る道の上にあるものが取れる。 -/
theorem child_toward {F : ParentForest} {root e : Nat} (h : F.Ancestor root e) :
    ∃ a, F.parent a = some root ∧ (F.Ancestor a e ∨ a = e) := by
  induction h with
  | direct hp => exact ⟨_, hp, Or.inr rfl⟩
  | step _ hpc ih =>
      obtain ⟨b, hb, hbe⟩ := ih
      refine ⟨b, hb, Or.inl ?_⟩
      rcases hbe with h1 | h1
      · exact ParentForest.Ancestor.step h1 hpc
      · subst h1
        exact ParentForest.Ancestor.direct hpc

end Yukito
