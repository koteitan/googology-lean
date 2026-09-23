/-
From koteitan, 1y-expand-equiv, `Equiv/FirstLive.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.RootGen

open Googology.Notation.Y

/-!
# 兄弟の差分と右隣

記号は `RootGen.lean` と同じ。`F` が frame、`U` がその上の値、
`Φ = restrictedParent F U` がその行の森である。「`q` が生きている」は
`Φ.parent q ≠ none` を指す。
-/

namespace Yukito

open OneY OneY.Numeric

variable {F : ParentForest} {U : Nat → Nat}

/-- 降下段。兄弟なら、差分の大小は元の値の大小と一致する。 -/
theorem sibling_descent (a : Row) {t q1 q2 : Nat}
    (h1 : a.forest.parent q1 = some t) (h2 : a.forest.parent q2 = some t) :
    a.difference q2 ≤ a.difference q1 ↔ a.value q2 ≤ a.value q1 := by
  have hv1 := a.parent_values h1
  have hv2 := a.parent_values h2
  simp only [Row.difference, h1, h2]
  omega

/-- `root` が `Φ` の子を持つなら、その右隣は生きている。 -/
def RootChildAdjacent (F : ParentForest) (U : Nat → Nat) : Prop :=
  ∀ root p, restrictedParent F U p = some root →
    restrictedParent F U (root + 1) ≠ none

/-- `e` が `root` の `F` 子で、`p` の `F` 祖先（または `p` 自身）なら、
`U e ≤ U j` から `U p ≤ U j` が出る。 -/
theorem one_of_nonancestor' {root p j e : Nat}
    (hp : restrictedParent F U p = some root)
    (he : F.parent e = some root)
    (hanc : ZeroY.Forest.Ancestor F.parent p e ∨ e = p)
    (hpos : 0 < U e)
    (hsib : U e ≤ U j) : U p ≤ U j := by
  have hre : root < e := F.parent_left he
  have h1 : U p ≤ U e := by
    rcases hanc with ha | heq
    · exact one_of_ancestor root p e hp ha hre hpos
    · subst heq; exact Nat.le_refl _
  omega

end Yukito
