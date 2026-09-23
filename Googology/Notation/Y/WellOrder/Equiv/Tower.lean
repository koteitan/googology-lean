/-
From koteitan, 1y-expand-equiv, `Equiv/Tower.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.FirstLive
import Googology.Notation.Y.WellOrder.Equiv.Row0

open Googology.Notation.Y

/-!
# 森の塔

行ごとの frame と値を 1 つの列にまとめる。層 `k` の frame の上に層 `k` の値を
載せると層 `k+1` の frame になる。

```
frameAt 0     = linearForest
frameAt (k+1) = (rows T.base k).forest
valAt k       = (rows T.base k).value
```
-/

namespace Yukito

open OneY OneY.Numeric

/-- 塔。底の frame と、その上に載る行。底についての 2 つの義務を持つ。

`ofSequence s` の塔では底の frame が線形森で、2 つの義務は自明である。抽出後の行の
塔では底の frame が `topForest` で、義務は `TopFrame.lean` で証明する。 -/
structure Tower where
  /-- 底の frame。 -/
  frame0 : ParentForest
  /-- その上に載る行。 -/
  base : Row
  /-- 行の森は底の frame 上の `restrictedParent`。 -/
  hbase : ∀ c, base.forest.parent c = restrictedParent frame0 base.value c
  /-- 値はすべて正。 -/
  hpos : ∀ c, 0 < base.value c
  /-- 底の義務 1：最左の子は右隣。 -/
  A0 : ∀ root e, frame0.parent e = some root → frame0.parent (root + 1) = some root
  /-- 底の義務 2：右隣の兄弟の単調性。 -/
  B0 : ∀ root e, frame0.parent (root + 1) = some root → frame0.parent e = some root →
        root + 1 < e → base.value e ≤ base.value (root + 1)

/-- 橋渡しの設定。塔と、列の上限。上限より右の列は値 1 で、行 1 以降では死ぬ。 -/
structure Setting where
  /-- 塔。 -/
  tower : Tower
  /-- 列の上限。 -/
  n : Nat
  /-- 上限より右の列の値は 1。 -/
  htail : ∀ c, n ≤ c → tower.base.value c = 1
  /-- 値の上限。段の数を押さえるのに使う。 -/
  bnd : Nat
  /-- 値は `bnd` 以下。 -/
  hbnd : ∀ c, tower.base.value c ≤ bnd

/-- 上限より右の列は行 1 以降で死んでいる。 -/
theorem setting_value_zero_of_ge (S : Setting) (r c : Nat) (hr : 0 < r) (h : S.n ≤ c) :
    (rows S.tower.base r).value c = 0 := by
  have h1 : (rows S.tower.base 1).value c = 0 := by
    show S.tower.base.difference c = 0
    have hn := Row.parent_none_of_one S.tower.base (S.htail c h)
    simp only [Row.difference, hn]
  have h2 : (rows S.tower.base r).value c ≤ (rows S.tower.base 1).value c :=
    rows_value_antitone S.tower.base hr c
  omega

/-- 層 `k` の frame。 -/
def frameAt (T : Tower) : Nat → ParentForest
  | 0 => T.frame0
  | k+1 => (rows T.base k).forest

/-- 層 `k` の値。 -/
def towerVal (T : Tower) (k : Nat) : Nat → Nat := (rows T.base k).value

/-- 塔の段。frame の上に値を載せると次の frame になる。 -/
theorem frameAt_step (T : Tower) (k : Nat) :
    (frameAt T (k+1)).parent = restrictedParent (frameAt T k) (towerVal T k) := by
  cases k with
  | zero => exact funext T.hbase
  | succ k => rfl

/-- 層 `k+1` の frame で兄弟なら、層 `k` での大小から層 `k+1` での大小が出る。 -/
theorem tower_case_descent (T : Tower) {k t q1 q2 : Nat}
    (h1 : (frameAt T (k+1)).parent q1 = some t)
    (h2 : (frameAt T (k+1)).parent q2 = some t)
    (hgoal : towerVal T k q2 ≤ towerVal T k q1) :
    towerVal T (k+1) q2 ≤ towerVal T (k+1) q1 :=
  (sibling_descent (rows T.base k) h1 h2).mpr hgoal

end Yukito
