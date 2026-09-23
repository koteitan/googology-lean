/-
From koteitan, 1y-expand-equiv, `Equiv/SibSucc.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Tower
import Googology.Notation.Y.WellOrder.Equiv.Chain

open Googology.Notation.Y

/-!
# 右隣の兄弟の単調性

山の段に残っていた 1 本を閉じる。示すのは次である。

```
root の restricted 親を共有する root+1 と e があり root+1 < e なら
  U e ≤ U (root+1)
```

一般の兄弟についてこれは**偽**である。効いているのは
片方が `root + 1`、すなわち `root` の右隣であるという条件である。

## 素直に降りると閉じない

層 `k` で兄弟なら差分の関係で目標は層 `k−1` に移る（`tower_case_descent`）。
ところが移った先で `e` は `root` の**子**とは限らず、`root` の子孫でしかない。
そこで 3 択（祖先・兄弟・どちらでもない）に分かれ、3 番目が閉じない。

## 引き上げてから降りる

一段下がる**前に** `e` を `root` の子まで引き上げる。`root` は層 `k` の frame で
`e` の祖先なので、`root` の子で `e` に至る道の上にあるもの `a` が取れる
（`child_toward`）。

* `a = root + 1` なら `root + 1` は `e` の祖先なので、`restrictedParent` の
  最大性がそのまま効いて終わる。
* `a ≠ root + 1` なら `root + 1 < a` であり、最大性から `U e ≤ U a` が出る。
  そして `a` と `root + 1` は **frame の親を共有する**ので、差分の関係で
  `U a ≤ U (root+1)` は一段下のまったく同じ主張になる。

つまり `e` を `a` に置き換えてから降りると、主張の形が層をまたいで変わらない。
3 択に分かれるのは `e` を引き上げずに降りたからであった。

## 段の対応

`frameAt T (m+1) = restrictedParent (frameAt T m) (towerVal T m)` なので、
`(frameAt T (m+1)).parent x = some root` は「層 `m` の restricted 親が `root`」
を意味する。結論の値は `towerVal T (m+1)` である。層を 1 つ取り違えると
成り立たなくなるので、両方を `SibSucc` の定義に明示する。

基底は層 0 である。`frameAt T 0` は線形森なので `root < q < e` なる列はすべて
`e` の祖先であり、最大性がそのまま効く。
-/

namespace Yukito

open OneY OneY.Numeric

/-- `restrictedParent` の親が `root` で、その列が `root + 1` なら、
frame の親も `root` である。祖先は `root + 1` 未満なので `root` 以下、
`root` 自身が祖先なので親はちょうど `root` になる。 -/
theorem fparent_of_succ {F : ParentForest} {U : Nat → Nat} {root : Nat}
    (hj : restrictedParent F U (root + 1) = some root) :
    F.parent (root + 1) = some root := by
  obtain ⟨ha, _, _, _⟩ := (restrictedParent_some_iff F U (root + 1) root).mp hj
  have ha' : F.Ancestor root (root + 1) := ParentForest.ancestor_of_zeroY ha
  obtain ⟨w, hw⟩ := ancestor_parent_exists' ha'
  have h1 : root ≤ w := ancestor_le_of_parent hw ha'
  have h2 : w < root + 1 := F.parent_left hw
  have hwe : w = root := by omega
  rw [hwe] at hw
  exact hw

/-- 底での 1 歩。`Φ0` の子 `e` について、`frame0` 親が `root` であることと
`V e ≤ V (root+1)` が同時に出る。塔の底の 2 つの義務をここで使う。 -/
theorem base_step (T : Tower) {root e : Nat}
    (h : restrictedParent T.frame0 (towerVal T 0) e = some root) :
    T.frame0.parent (root + 1) = some root ∧
      towerVal T 0 e ≤ towerVal T 0 (root + 1) := by
  obtain ⟨hanc, hposr, hltv, hmax⟩ :=
    (restrictedParent_some_iff T.frame0 (towerVal T 0) e root).mp h
  obtain ⟨a, hFa, hae⟩ := child_toward (ParentForest.ancestor_of_zeroY hanc)
  have hFj : T.frame0.parent (root + 1) = some root := T.A0 root a hFa
  have hra : root < a := T.frame0.parent_left hFa
  have hea : towerVal T 0 e ≤ towerVal T 0 a := by
    rcases hae with ha | heq
    · rcases Nat.lt_or_ge (towerVal T 0 a) (towerVal T 0 e) with hx | hx
      · have := hmax a (ParentForest.ancestor_to_zeroY ha) (T.hpos a) hx
        omega
      · exact hx
    · rw [heq]
      exact Nat.le_refl _
  have haj : towerVal T 0 a ≤ towerVal T 0 (root + 1) := by
    rcases Nat.lt_or_ge (root + 1) a with hx | hx
    · exact T.B0 root a hFj hFa hx
    · have heqa : a = root + 1 := by omega
      rw [heqa]
      exact Nat.le_refl _
  exact ⟨hFj, by omega⟩

/-- liveness の正確な段。層 `m+1` の frame で親を持つことと、
層 `m+1` の値が正であることは同値である。 -/
theorem frame_parent_iff_pos (T : Tower) (m q : Nat) :
    (∃ z, (frameAt T (m + 1)).parent q = some z) ↔ 0 < towerVal T (m + 1) q :=
  rows_parent_iff_next_live T.base m q

/-- 層 `m` の主張。`root` の restricted 子である `root+1` と `e` について、
一段上の値で単調性が成り立つ。 -/
def SibSucc (T : Tower) (m : Nat) : Prop :=
  ∀ root e, (frameAt T (m + 1)).parent (root + 1) = some root →
    (frameAt T (m + 1)).parent e = some root → root + 1 < e →
      towerVal T (m + 1) e ≤ towerVal T (m + 1) (root + 1)

/-- **山の段の残り 1 本。** 数列の要素がすべて正なら、すべての層で成り立つ。 -/
theorem sibSucc (T : Tower) : ∀ m, SibSucc T m := by
  intro m
  induction m with
  | zero =>
    intro root e h1 h2 hlt
    refine tower_case_descent T h1 h2 ?_
    rw [frameAt_step] at h2
    exact (base_step T h2).2
  | succ m ih =>
    intro root e h1 h2 hlt
    refine tower_case_descent T h1 h2 ?_
    rw [frameAt_step] at h1 h2
    -- `F = frameAt T (m+1)`、`U = towerVal T (m+1)`
    have hFj : (frameAt T (m + 1)).parent (root + 1) = some root := fparent_of_succ h1
    have hposj : 0 < towerVal T (m + 1) (root + 1) :=
      (frame_parent_iff_pos T m (root + 1)).mp ⟨root, hFj⟩
    have hanc : (frameAt T (m + 1)).Ancestor root e :=
      ParentForest.ancestor_of_zeroY
        ((restrictedParent_some_iff _ _ e root).mp h2).1
    obtain ⟨a, hFa, hae⟩ := child_toward hanc
    have hra : root < a := (frameAt T (m + 1)).parent_left hFa
    by_cases haj : a = root + 1
    · subst haj
      rcases hae with hanc' | heq
      · exact one_of_ancestor root e (root + 1) h2
          (ParentForest.ancestor_to_zeroY hanc') hra hposj
      · exact absurd heq (by omega)
    · have hlta : root + 1 < a := by omega
      have hposa : 0 < towerVal T (m + 1) a :=
        (frame_parent_iff_pos T m a).mp ⟨root, hFa⟩
      have hea : towerVal T (m + 1) e ≤ towerVal T (m + 1) a := by
        rcases hae with hanc' | heq
        · exact one_of_ancestor root e a h2
            (ParentForest.ancestor_to_zeroY hanc') hra hposa
        · rw [heq]
          exact Nat.le_refl _
      have haj' : towerVal T (m + 1) a ≤ towerVal T (m + 1) (root + 1) :=
        ih root a hFj hFa hlta
      omega

/-! ## 山の段への接続

`SibSucc` は行の形で書き直せる。`frameAt T (m+1) = (rows T.base m).forest`、
`towerVal T (m+1) = (rows T.base (m+1)).value` がどちらも定義そのままだから
である。これを `one_of_nonancestor'` に入れると、残っていた仮定 `hsib` が消える。 -/

/-- 行の形で書いた `SibSucc`。 -/
theorem sibSucc_rows (T : Tower) (m root e : Nat)
    (hj : (rows T.base m).forest.parent (root + 1) = some root)
    (he : (rows T.base m).forest.parent e = some root)
    (hlt : root + 1 < e) :
    (rows T.base (m + 1)).value e ≤
      (rows T.base (m + 1)).value (root + 1) :=
  sibSucc T m root e hj he hlt

/-! ## 最左の子は右隣（`RootChildAdjacent`）

`SibSucc` があると、次が層に関する帰納で出る。

```
root が層 k の frame で子を持つなら、frame での root+1 の親は root である
```

すなわち **`root` の最左の子は `root + 1`** である。これは `RootChildAdjacent`
そのもので、JS の `firstAtLeast` が指す列が `root + 1` であることを与える。

帰納の 1 段はこうである。`e` を `root` の restricted 子とすると、`root` は
frame で `e` の祖先なので、`root` の frame 子 `a` で `e` に至る道の上にあるものが
取れる。1 つ下の段の主張から `root + 1` も `root` の frame 子である。あとは

```
W e ≤ W a        restrictedParent の最大性（a は e の祖先）
W a ≤ W (root+1) SibSucc（a と root+1 は frame 兄弟で root+1 ≤ a）
W root < W e     e の親が root であること
```

を繋いで `W root < W (root+1)` を得る。`root` は `root+1` の frame 親なので
最も右の祖先でもあり、restricted 親の条件をすべて満たす。 -/

/-- **最左の子は右隣。** `root` が層 `k+1` の frame で子を持つなら、
`root + 1` もその子である。 -/
theorem leftmost_child (T : Tower) :
    ∀ k root e, (frameAt T (k + 1)).parent e = some root →
      (frameAt T (k + 1)).parent (root + 1) = some root := by
  intro k
  induction k with
  | zero =>
    intro root e h
    rw [frameAt_step] at h ⊢
    obtain ⟨hanc, hpr, hlt, _⟩ := (restrictedParent_some_iff _ _ e root).mp h
    obtain ⟨hFj, hej⟩ := base_step T h
    refine (restrictedParent_some_iff _ _ (root + 1) root).mpr
      ⟨ParentForest.ancestor_to_zeroY (ParentForest.Ancestor.direct hFj), hpr,
        by omega, ?_⟩
    intro q hq _ _
    exact ancestor_le_of_parent hFj (ParentForest.ancestor_of_zeroY hq)
  | succ k ih =>
    intro root e h
    rw [frameAt_step] at h ⊢
    obtain ⟨hanc, hpr, hlt, hmax⟩ := (restrictedParent_some_iff _ _ e root).mp h
    obtain ⟨a, hFa, hae⟩ := child_toward (ParentForest.ancestor_of_zeroY hanc)
    have hra : root < a := (frameAt T (k + 1)).parent_left hFa
    have hFj : (frameAt T (k + 1)).parent (root + 1) = some root := ih root a hFa
    have hposa : 0 < towerVal T (k + 1) a :=
      (frame_parent_iff_pos T k a).mp ⟨root, hFa⟩
    have hea : towerVal T (k + 1) e ≤ towerVal T (k + 1) a := by
      rcases hae with ha' | heq
      · rcases Nat.lt_or_ge (towerVal T (k + 1) a) (towerVal T (k + 1) e) with hx | hx
        · have := hmax a (ParentForest.ancestor_to_zeroY ha') hposa hx
          omega
        · exact hx
      · rw [heq]
        exact Nat.le_refl _
    have haj : towerVal T (k + 1) a ≤ towerVal T (k + 1) (root + 1) := by
      rcases Nat.lt_or_ge (root + 1) a with hx | hx
      · exact sibSucc T k root a hFj hFa hx
      · have heq : a = root + 1 := by omega
        rw [heq]
        exact Nat.le_refl _
    refine (restrictedParent_some_iff _ _ (root + 1) root).mpr
      ⟨ParentForest.ancestor_to_zeroY (ParentForest.Ancestor.direct hFj), hpr,
        by omega, ?_⟩
    intro q hq _ _
    exact ancestor_le_of_parent hFj (ParentForest.ancestor_of_zeroY hq)

/-- **`RootChildAdjacent` は山のすべての層で成り立つ。** -/
theorem rootChildAdjacent_tower (T : Tower) (k : Nat) :
    RootChildAdjacent (frameAt T k) (towerVal T k) := by
  intro root p hp
  rw [← frameAt_step] at hp ⊢
  rw [leftmost_child T k root p hp]
  intro hn
  cases hn

/-- 行の形。`root` が行 `k` の森で子を持つなら、`root + 1` もその子である。 -/
theorem leftmost_child_rows (T : Tower) (k root e : Nat)
    (h : (rows T.base k).forest.parent e = some root) :
    (rows T.base k).forest.parent (root + 1) = some root :=
  leftmost_child T k root e h

/-! ## 層 0 まで込めた形

`frameAt T 0` は線形森なので、`root` の子は `root + 1` しかない。したがって
`SibSucc` の仮定（`root+1 < e` かつ両方が `root` の子）は層 0 では満たせず、
主張は空虚に成り立つ。`leftmost_child` も層 0 では自明である。これで層の場合分けを
1 か所に閉じ込められる。 -/

/-- 層 0 まで込めた `leftmost_child`。 -/
theorem leftmost_child_all (T : Tower) (r root e : Nat)
    (h : (frameAt T r).parent e = some root) :
    (frameAt T r).parent (root + 1) = some root := by
  cases r with
  | zero => exact T.A0 root e h
  | succ k => exact leftmost_child T k root e h

/-- 層 0 まで込めた `sibSucc`。 -/
theorem sibSucc_all (T : Tower) (r root e : Nat)
    (hj : (frameAt T r).parent (root + 1) = some root)
    (he : (frameAt T r).parent e = some root) (hlt : root + 1 < e) :
    towerVal T r e ≤ towerVal T r (root + 1) := by
  cases r with
  | zero => exact T.B0 root e hj he hlt
  | succ k => exact sibSucc T k root e hj he hlt

/-- 層 0 まで込めた liveness。親を持つ列はその層で値が正である。 -/
theorem towerVal_pos_of_parent (T : Tower) (r q : Nat)
    (h : ∃ z, (frameAt T r).parent q = some z) : 0 < towerVal T r q := by
  cases r with
  | zero => exact T.hpos q
  | succ k => exact (frame_parent_iff_pos T k q).mp h

/-- **非祖先の場合の (1)。全層で成り立つ形。** -/
theorem one_of_nonancestor_tower (T : Tower) (r : Nat)
    {root p e : Nat}
    (hp : (frameAt T (r + 1)).parent p = some root)
    (he : (frameAt T r).parent e = some root)
    (hanc : ZeroY.Forest.Ancestor (frameAt T r).parent p e ∨ e = p) :
    towerVal T r p ≤ towerVal T r (root + 1) := by
  rw [frameAt_step] at hp
  have hj := leftmost_child_all T r root e he
  have hposE := towerVal_pos_of_parent T r e ⟨root, he⟩
  have hsib : towerVal T r e ≤ towerVal T r (root + 1) := by
    rcases Nat.lt_or_ge (root + 1) e with hlt | hge
    · exact sibSucc_all T r root e hj he hlt
    · have hre := (frameAt T r).parent_left he
      have heq : e = root + 1 := by omega
      rw [heq]
      exact Nat.le_refl _
  exact one_of_nonancestor' hp he hanc hposE hsib

/-! ## 線形森を底とする塔

入力列から作る塔。底の frame は線形森で、2 つの義務は自明に成り立つ。
入力列についての定理は、この塔での特殊化として得る。 -/

/-- 線形森で親が `root` なら、その列は `root + 1` である。 -/
theorem linear_child_eq {root e : Nat}
    (h : (linearForest : ParentForest).parent e = some root) : e = root + 1 := by
  cases e with
  | zero => cases h
  | succ n => exact congrArg Nat.succ (Option.some.inj h)

/-- 入力列から作る塔。 -/
def linearTower (s : List Nat) (hs : ∀ x ∈ s, 0 < x) : Tower where
  frame0 := linearForest
  base := ofSequence s
  hbase := fun _ => rfl
  hpos := ofSequence_positive s hs
  A0 := fun _ _ h => by rw [← linear_child_eq h]; exact h
  B0 := fun _ e _ he hlt => by
    have hce := linear_child_eq he
    omega

end Yukito
