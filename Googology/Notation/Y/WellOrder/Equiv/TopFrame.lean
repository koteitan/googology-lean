/-
From koteitan, 1y-expand-equiv, `Equiv/TopFrame.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Mountain
import Googology.Notation.Y.WellOrder.OneY.PseudoSelection

open Googology.Notation.Y

/-!
# 抽出後の行の下にある frame

抽出を繰り返すには、橋渡しを「一般の行から作る山」へ広げる必要がある。そのとき
塔の底に来るのは、`ofSequence` のときの線形森ではなく、抽出後の行の下にある frame
である。

Phyrion は `rawExtract` の親が `topForest` 上の `restrictedParent` に一致することを
示している（`rawExtract_parent_eq_topForest`）。`topForest` は

```
topForest.parent c = if height c = 0 then none else some (rootAt (height c − 1) c)
```

で、「頂の 1 つ下の段での成分の根」である。擬親森より構造がはっきりしていて、
山の段で証明した道具がそのまま効く。

本ファイルは底の義務の 1 本目、**最左の子は右隣**を `topForest` について示す。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-- 塔の底から作る Phyrion 側の山。 -/
def mountainOfT (T : Tower) : RowMountain := mountain T.base T.hpos

theorem mountainOfT_height_eq (T : Tower) (c : Nat) :
    (mountainOfT T).height c = height T.base c := rfl

theorem mountainOfT_rootAt_eq (T : Tower) (r c : Nat) :
    (mountainOfT T).rootAt r c = (rows T.base r).forest.root c := rfl

/-- 頂の 1 つ上の段では、頂の根はもう親を持たない。 -/
theorem height_succ_of_leftmost (T : Tower) (root : Nat)
    (hn : (rows T.base (height T.base root)).forest.parent root = none)
    (hf : (rows T.base (height T.base root)).forest.parent (root + 1)
      = some root) :
    height T.base (root + 1) = height T.base root + 1 := by
  have hlive : 0 < (rows T.base
      (height T.base root + 1)).value (root + 1) :=
    (rows_parent_iff_next_live T.base _ (root + 1)).mp ⟨root, hf⟩
  have hge : height T.base root + 1 ≤ height T.base (root + 1) :=
    (live_iff_le_height T.base (T.hpos (root + 1)) _).mp hlive
  have hle : height T.base (root + 1) ≤ height T.base root + 1 := by
    rcases Nat.lt_or_ge (height T.base root + 1)
      (height T.base (root + 1)) with hlt | hle
    · exfalso
      -- 行 `H root + 1` で `root+1` が親を持つことになるが、その親は
      -- 行 `H root` での祖先、すなわち `root` しかなく、`root` はそこで死んでいる
      obtain ⟨q, hq⟩ := (parent_exists_iff_lt_height T.base
        (T.hpos (root + 1)) (height T.base root + 1)).mpr hlt
      have hq' : restrictedParent (rows T.base (height T.base root)).forest
          (rows T.base (height T.base root + 1)).value (root + 1)
          = some q := hq
      obtain ⟨hanc, hpos, _, _⟩ :=
        (restrictedParent_some_iff _ _ (root + 1) q).mp hq'
      -- `q` は行 `H root` で `root+1` の祖先。祖先は `root` のみ
      have hqr : q = root := by
        rcases ancestor_cases hf (ParentForest.ancestor_of_zeroY hanc) with he | ha
        · exact he
        · exact absurd (ancestor_parent_exists' ha) (by rw [hn]; rintro ⟨t, ht⟩; cases ht)
      rw [hqr] at hpos
      have hdead : (rows T.base (height T.base root + 1)).value root = 0 := by
        rcases Nat.eq_zero_or_pos
          ((rows T.base (height T.base root + 1)).value root) with h | h
        · exact h
        · exact absurd ((live_iff_le_height T.base
            (T.hpos root) _).mp h) (by omega)
      omega
    · exact hle
  omega

/-- **底の義務 1。** `topForest` でも最左の子は右隣である。 -/
theorem topForest_leftmost_child (T : Tower) (root e : Nat)
    (h : (mountainOfT T).topForest.parent e = some root) :
    (mountainOfT T).topForest.parent (root + 1) = some root := by
  obtain ⟨hHe, hroot⟩ :=
    (RowMountain.topForest_parent_some_iff (mountainOfT T) e root).mp h
  rw [mountainOfT_height_eq] at hHe
  rw [mountainOfT_height_eq, mountainOfT_rootAt_eq] at hroot
  -- `H root = H e − 1`
  have hHr : height T.base root = height T.base e - 1 := by
    have hrh := (mountainOfT T).root_height
      (show height T.base e - 1 ≤ (mountainOfT T).height e by
        rw [mountainOfT_height_eq]; omega) (c := e)
    rw [mountainOfT_height_eq, mountainOfT_rootAt_eq, hroot] at hrh
    exact hrh
  have hlt : root < e := by
    have hrl := (mountainOfT T).rootAt_lt
      (show height T.base e - 1 < (mountainOfT T).height e by
        rw [mountainOfT_height_eq]; omega) (c := e)
    rw [mountainOfT_rootAt_eq, hroot] at hrl
    exact hrl
  -- `root` は行 `H root` で `e` の祖先
  have hanc : (rows T.base (height T.base root)).forest.Ancestor root e := by
    have hpath := ((mountainOfT T).rootAt_eq_iff_path
      (r := height T.base e - 1) (q := root) (c := e)
      (by rw [mountainOfT_height_eq]; omega)).mp
      (by rw [mountainOfT_rootAt_eq]; exact hroot)
    rcases hpath with ha | he
    · rw [hHr]
      exact ha
    · omega
  obtain ⟨a, hFa, _⟩ := child_toward hanc
  have hf := leftmost_child_rows T (height T.base root) root a hFa
  have hn : (rows T.base (height T.base root)).forest.parent root = none := by
    cases hp : (rows T.base (height T.base root)).forest.parent root with
    | none => rfl
    | some q =>
        exfalso
        have := (parent_exists_iff_lt_height T.base
          (T.hpos root) (height T.base root)).mp ⟨q, hp⟩
        omega
  have hH1 := height_succ_of_leftmost T root hn hf
  refine (RowMountain.topForest_parent_some_iff (mountainOfT T) (root + 1) root).mpr
    ⟨by rw [mountainOfT_height_eq]; omega, ?_⟩
  rw [mountainOfT_height_eq, mountainOfT_rootAt_eq, hH1,
    show height T.base root + 1 - 1 = height T.base root from by omega,
    (rows T.base (height T.base root)).forest.root_of_parent_some hf]
  exact (rows T.base (height T.base root)).forest.root_of_parent_none hn

/-- `topForest` の親から、段の関係を読む。 -/
theorem topForest_heights (T : Tower) (root e : Nat)
    (h : (mountainOfT T).topForest.parent e = some root) :
    height T.base e = height T.base root + 1 ∧
      root < e ∧
      (rows T.base (height T.base root)).forest.Ancestor root e := by
  obtain ⟨hHe, hroot⟩ :=
    (RowMountain.topForest_parent_some_iff (mountainOfT T) e root).mp h
  rw [mountainOfT_height_eq] at hHe
  rw [mountainOfT_height_eq, mountainOfT_rootAt_eq] at hroot
  have hHr : height T.base root = height T.base e - 1 := by
    have hrh := (mountainOfT T).root_height
      (show height T.base e - 1 ≤ (mountainOfT T).height e by
        rw [mountainOfT_height_eq]; omega) (c := e)
    rw [mountainOfT_height_eq, mountainOfT_rootAt_eq, hroot] at hrh
    exact hrh
  have hlt : root < e := by
    have hrl := (mountainOfT T).rootAt_lt
      (show height T.base e - 1 < (mountainOfT T).height e by
        rw [mountainOfT_height_eq]; omega) (c := e)
    rw [mountainOfT_rootAt_eq, hroot] at hrl
    exact hrl
  refine ⟨by omega, hlt, ?_⟩
  have hpath := ((mountainOfT T).rootAt_eq_iff_path
    (r := height T.base e - 1) (q := root) (c := e)
    (by rw [mountainOfT_height_eq]; omega)).mp
    (by rw [mountainOfT_rootAt_eq]; exact hroot)
  rcases hpath with ha | he
  · rw [hHr]
    exact ha
  · omega

/-- **底の義務 2。** `topForest` の子 `root+1` と `e`（`root+1 < e`）について
`topValue e ≤ topValue (root+1)`。

`topForest` の親が `root` なら段はちょうど `H root + 1` なので、両方の `topValue` は
その段の値である。`e` はその段が頂なので次の段では親を持たず、`restrictedParent` の
最大性から `root` の子 `a`（`e` へ至る道の上）について `V e ≤ V a`。あとは
`sibSucc_rows` で `V a ≤ V (root+1)` を繋ぐ。 -/
theorem topForest_sibSucc (T : Tower) (root e : Nat)
    (hj : (mountainOfT T).topForest.parent (root + 1) = some root)
    (he : (mountainOfT T).topForest.parent e = some root)
    (_hlt : root + 1 < e) :
    topValue T.base e ≤ topValue T.base (root + 1) := by
  obtain ⟨hHe, _, hanc⟩ := topForest_heights T root e he
  obtain ⟨hHj, _, _⟩ := topForest_heights T root (root + 1) hj
  -- 両方の頂は段 `H root + 1`
  have hve : topValue T.base e
      = (rows T.base (height T.base root + 1)).value e := by
    show (rows T.base (height T.base e)).value e = _
    rw [hHe]
  have hvj : topValue T.base (root + 1)
      = (rows T.base (height T.base root + 1)).value (root + 1) := by
    show (rows T.base (height T.base (root + 1))).value (root + 1) = _
    rw [hHj]
  rw [hve, hvj]
  -- `root` の子 `a` で `e` に至る道の上にあるもの
  obtain ⟨a, hFa, hae⟩ := child_toward hanc
  have hja := leftmost_child_rows T (height T.base root) root a hFa
  have hapos : 0 < (rows T.base (height T.base root + 1)).value a :=
    (rows_parent_iff_next_live T.base _ a).mp ⟨root, hFa⟩
  -- `e` はこの段が頂なので次の段で親を持たない
  have hnone : (rows T.base (height T.base root + 1)).forest.parent e
      = none := by
    cases hp : (rows T.base (height T.base root + 1)).forest.parent e with
    | none => rfl
    | some q =>
        exfalso
        have := (parent_exists_iff_lt_height T.base
          (T.hpos e) (height T.base root + 1)).mp ⟨q, hp⟩
        omega
  have hea : (rows T.base (height T.base root + 1)).value e
      ≤ (rows T.base (height T.base root + 1)).value a := by
    rcases hae with ha' | heq
    · exact (restrictedParent_none_iff (rows T.base (height T.base root)).forest
        (rows T.base (height T.base root + 1)).value e).mp hnone a ha' hapos
    · rw [heq]
      exact Nat.le_refl _
  have haj : (rows T.base (height T.base root + 1)).value a
      ≤ (rows T.base (height T.base root + 1)).value (root + 1) := by
    rcases Nat.lt_or_ge (root + 1) a with hx | hx
    · exact sibSucc_rows T (height T.base root) root a hja hFa hx
    · have hra := (rows T.base (height T.base root)).forest.parent_left hFa
      have heqa : a = root + 1 := by omega
      rw [heqa]
      exact Nat.le_refl _
  omega

/-! ## 抽出後の行の塔

底の 2 つの義務が揃ったので、抽出後の行を底とする塔を組み立てられる。これで
山の段の定理がそのまま抽出後の行にも効く。 -/

/-- 塔を 1 回抽出した塔。底の frame は `topForest`。 -/
def extractTowerOf (T : Tower) : Tower where
  frame0 := (mountainOfT T).topForest
  base := rawExtract T.base T.hpos
  hbase := fun c => rawExtract_parent_eq_topForest T.base T.hpos c
  hpos := fun c => topValue_pos T.base (T.hpos c)
  A0 := topForest_leftmost_child T
  B0 := topForest_sibSucc T

end Yukito
